package main

import (
	"fmt"
	"io"
	"net/http"

	"github.com/gorilla/mux"
)

// Validate the ownership of the ID
// Header "Authorization: ID" matches the supplied path ID
// e.g. curl -v localhost:8000/account/123 -H "Authorization: 123"
// In a real-world implementation, "Authorization: ID" would be a JWT claim
func AuthorizationMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		profile := r.Header.Get("Authorization")
		if len(profile) == 0 {
			fmt.Println("missing auth token")
			rw.WriteHeader(401)
			return
		}
		tokenID := mux.Vars(r)["id"]
		// This comparison is an error handler;  it could also be written as
		// if profile == tokenID ...
		if profile != tokenID {
			fmt.Println("ownership not matched")
			rw.WriteHeader(401)
			return
		}
		next.ServeHTTP(rw, r)
	})
}


func AuthorizationMiddleware_Bad(next http.Handler) http.Handler {
	return http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		profile := r.Header.Get("Authorization")
		if len(profile) == 0 {
			fmt.Println("missing auth token")
			rw.WriteHeader(401)
			return
		}
		tokenID := mux.Vars(r)["id"]
		next.ServeHTTP(rw, r)
	})
}



func GetAccount(rw http.ResponseWriter, r *http.Request) {
	io.WriteString(rw, `{"message": "hello world.."}`)
}

func main_bad() {
	fmt.Println("running...")
	router := mux.NewRouter()
	/* signature expected by Handle:
	Handle(path string, handler http.Handler) *Route, so
	we always have a HandlerFunc()
	*/
	router.Handle("/account/{id}", http.HandlerFunc(GetAccount))
	/*
		cannot use GetAccount (value of type func(rw http.ResponseWriter, r *http.Request)) as http.Handler value in argument to router.Handle: missing method

		router.Handle("/account/{id}", GetAccount)
	*/
	http.Handle("/", router)
	http.ListenAndServe(":8000", router)
}

/*
	Bad flow:
	http.HandlerFunc(GetAccount) -> router.Handle

	OK flow:
	http.HandlerFunc(GetAccount) ->  AuthorizationMiddleware() -> router.Handle()

	We Want to find the bad flow.

	If we treat AuthorizationMiddleware (the concept, not the particular function) as sanitizer, the ok flow won't show.

*/
func main() {
	fmt.Println("running...")
	router := mux.NewRouter()
	router.Handle("/account/{id}", AuthorizationMiddleware(http.HandlerFunc(GetAccount)))
	http.Handle("/", router)
	http.ListenAndServe(":8000", router)
}


func main_bad2() {
	fmt.Println("running...")
	router := mux.NewRouter()
	/* signature expected by Handle:
	Handle(path string, handler http.Handler) *Route, so
	we always have a HandlerFunc()
	*/
	router.Handle("/account/{id}",  AuthorizationMiddleware_Bad(http.HandlerFunc(GetAccount)))
	/*
		cannot use GetAccount (value of type func(rw http.ResponseWriter, r *http.Request)) as http.Handler value in argument to router.Handle: missing method

		router.Handle("/account/{id}", GetAccount)
	*/
	http.Handle("/", router)
	http.ListenAndServe(":8000", router)
}
