// Command gitserver serves git repositories over HTTP with basic
// authentication, for the end-to-end test. A push creates a repository
// that doesn't exist yet.
package main

import (
	"errors"
	"flag"
	"log"
	"net/http"
	"os"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
)

func main() {
	addr := flag.String("addr", ":8418", "address to serve on")
	root := flag.String("root", "", "directory that holds the repositories")
	username := flag.String("username", "git-k8s", "username that requests must send")
	flag.Parse()
	password := os.Getenv("GITSERVER_PASSWORD")
	if *root == "" || password == "" {
		log.Fatal("set -root and GITSERVER_PASSWORD")
	}
	srv := &http.Server{
		Addr:              *addr,
		Handler:           &gitserver.Server{Root: *root, Username: *username, Password: password},
		ReadHeaderTimeout: 10 * time.Second,
	}
	log.Printf("serving %s on %s", *root, *addr)
	if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
		log.Fatal(err)
	}
}
