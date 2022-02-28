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
	return http.HandlerFunc(func(rw http.ResponseWriter, req *http.Request) {
		profile := req.Header.Get("Authorization")
		if len(profile) == 0 {
			fmt.Println("missing auth token")
			rw.WriteHeader(401)
			return
		}
		tokenID := mux.Vars(req)["id"]
		// This comparison is an error handler;  it could also be written as
		// if profile == tokenID ...
		if profile != tokenID {
			fmt.Println("ownership not matched")
			rw.WriteHeader(401)
			return
		}
		next.ServeHTTP(rw, req)
	})
}

func AuthorizationMiddleware_Bad(next http.Handler) http.Handler {
	return http.HandlerFunc(func(rw http.ResponseWriter, req *http.Request) {
		profile := req.Header.Get("Authorization")
		if len(profile) == 0 {
			fmt.Println("missing auth token")
			rw.WriteHeader(401)
			return
		}
		tokenID := mux.Vars(req)["id"]
		fmt.Println("tokenID: " + tokenID)
		next.ServeHTTP(rw, req)
	})
}

func GetAccount(rw http.ResponseWriter, req *http.Request) {
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
		cannot use GetAccount (value of type func(rw http.ResponseWriter, req *http.Request)) as http.Handler value in argument to router.Handle: missing method

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
func main_good() {
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
	router.Handle("/account/{id}", AuthorizationMiddleware_Bad(http.HandlerFunc(GetAccount)))
	/*
		cannot use GetAccount (value of type func(rw http.ResponseWriter, req *http.Request)) as http.Handler value in argument to router.Handle: missing method

		router.Handle("/account/{id}", GetAccount)
	*/
	http.Handle("/", router)
	http.ListenAndServe(":8000", router)
}

///
// Middleware as array/slice of HandlerFuncs example
///

// A Middleware is a type of http.HandlerFunc
type Middleware func(http.HandlerFunc) http.HandlerFunc

func LoggingFunc() Middleware {
	return func(next http.HandlerFunc) http.HandlerFunc {
		return func(w http.ResponseWriter, req *http.Request) {
			// Logging middleware
			fmt.Println(req)
			defer func() {
				if _, ok := recover().(error); ok {
					w.WriteHeader(http.StatusInternalServerError)
				}
			}()

			// Call next middleware/handler in chain
			next(w, req)
		}
	}
}

func AuthFunc() Middleware {
	return func(next http.HandlerFunc) http.HandlerFunc {
		return func(w http.ResponseWriter, req *http.Request) {
			profile := req.Header.Get("Authorization")
			if len(profile) == 0 {
				fmt.Println("missing auth token")
				w.WriteHeader(401)
				return
			}
			tokenID := mux.Vars(req)["id"]
			if profile != tokenID {
				fmt.Println("ownership not matched")
				w.WriteHeader(401)
				return
			}
			fmt.Println("tokenID: " + tokenID)
			next(w, req)
		}
	}
}

func SayHello(w http.ResponseWriter, req *http.Request) {
	fmt.Fprintln(w, "Hello client")
}

// Chain applies a slice of middleware handler funcss
func Chain(f http.HandlerFunc, middlewares ...Middleware) http.HandlerFunc {
	for _, m := range middlewares {
		f = m(f)
	}
	return f
}

// Create a server that uses a "chain" of middlware handlers
func main_chain() {
	r := mux.NewRouter()

	// execute middleware from right to left of the chain
	chain := Chain(SayHello, AuthFunc(), LoggingFunc())
	r.HandleFunc("/account/{id}", chain)

	fmt.Println("server listening: 8000")
	http.ListenAndServe(":8000", r)
}

///
// mux.MiddlewareFunc example
///
func MWAuthFunc(r *mux.Router) mux.MiddlewareFunc {
	return func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
			profile := req.Header.Get("Authorization")
			if len(profile) == 0 {
				fmt.Println("missing auth token")
				w.WriteHeader(401)
				return
			}
			tokenID := mux.Vars(req)["id"]
			if profile != tokenID {
				fmt.Println("ownership not matched")
				w.WriteHeader(401)
				return
			}
			fmt.Println("tokenID: " + tokenID)

			next.ServeHTTP(w, req)
		})
	}
}

func MWSayHello(r *mux.Router) mux.MiddlewareFunc {
	return func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
			fmt.Fprintln(w, "Hello client")
			next.ServeHTTP(w, req)
		})
	}
}

// Create a server that with a middleware chain via mux.Use()
func main_uses_chain() {
	r := mux.NewRouter()

	r.HandleFunc("/account/{id}", SayHello).Methods(http.MethodGet)
	r.Use(MWAuthFunc(r))

	fmt.Println("server listening: 8000")
	http.ListenAndServe(":8000", r)
}

///
// Actual main: call the appropriate sub-main
func main() {
	main_uses_chain()
}
