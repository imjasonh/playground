// Command gitserver serves git repositories over HTTP with basic
// authentication, for the end-to-end test. A push creates a repository
// that doesn't exist yet. With -allowed-signers, the server rejects pushes
// of commits that aren't signed, as a forge that requires signed commits
// does.
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
	kubeContext := flag.String("kube-context", "", "kubectl context whose API server reviews the service account tokens that a fake Octo STS under /github/ receives; without it, /github/ isn't served")
	username := flag.String("username", "git-k8s", "username that requests must send")
	goProxy := flag.String("goproxy", "", "directory to serve as a Go module proxy at /proxy/, without authentication")
	allowedSigners := flag.String("allowed-signers", "", "allowed signers file; when set, every commit that a push adds must be signed with the key that the file lists for its committer email")
	flag.Parse()
	password := os.Getenv("GITSERVER_PASSWORD")
	if *root == "" || password == "" {
		log.Fatal("set -root and GITSERVER_PASSWORD")
	}
	var h http.Handler = &gitserver.Server{Root: *root, Username: *username, Password: password, AllowedSigners: *allowedSigners}
	if *goProxy != "" {
		mux := http.NewServeMux()
		mux.Handle("/proxy/", http.StripPrefix("/proxy", http.FileServer(http.Dir(*goProxy))))
		mux.Handle("/", h)
		h = mux
	}
	srv := &http.Server{
		Addr:              *addr,
		Handler:           h,
		ReadHeaderTimeout: 10 * time.Second,
	}
	if *kubeContext != "" {
		srv.Handler = withGitHub(srv.Handler, *root, *username, password, *allowedSigners, *kubeContext)
	}
	log.Printf("serving %s on %s", *root, *addr)
	if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
		log.Fatal(err)
	}
}
