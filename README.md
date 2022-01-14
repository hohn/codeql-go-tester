## CodeQL Go Example


### Create the CodeQL database
```
export PATH="$HOME/local/vmsync/codeql263:$PATH"
codeql database create --language="go" ./sample-db --overwrite
```

### Build and run
```
$ go run main.go
```
