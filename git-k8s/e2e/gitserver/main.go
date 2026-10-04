// Command gitserver serves git repositories over HTTP with basic
// authentication, and over SSH if -ssh-addr is set, for the end-to-end
// test. A push creates a repository that doesn't exist yet.
package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"log"
	"net"
	"net/http"
	"os"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/git-k8s/internal/gitserver"
)

func main() {
	addr := flag.String("addr", ":8418", "address to serve on")
	root := flag.String("root", "", "directory that holds the repositories")
	username := flag.String("username", "git-k8s", "username that requests must send")
	sshAddr := flag.String("ssh-addr", "", "address to serve SSH on, if any")
	hostKey := flag.String("ssh-host-key", "", "file that holds the SSH server's private host key")
	authorizedKeys := flag.String("ssh-authorized-keys", "", "file that lists the keys that SSH clients can use, in authorized_keys format")
	flag.Parse()
	password := os.Getenv("GITSERVER_PASSWORD")
	if *root == "" || password == "" {
		log.Fatal("set -root and GITSERVER_PASSWORD")
	}
	errs := make(chan error, 2)
	if *sshAddr != "" {
		s, err := sshServer(*root, *hostKey, *authorizedKeys)
		if err != nil {
			log.Fatal(err)
		}
		l, err := net.Listen("tcp", *sshAddr)
		if err != nil {
			log.Fatal(err)
		}
		log.Printf("serving %s over SSH on %s", *root, *sshAddr)
		go func() { errs <- s.Serve(l) }()
	}
	srv := &http.Server{
		Addr:              *addr,
		Handler:           &gitserver.Server{Root: *root, Username: *username, Password: password},
		ReadHeaderTimeout: 10 * time.Second,
	}
	log.Printf("serving %s on %s", *root, *addr)
	go func() { errs <- srv.ListenAndServe() }()
	log.Fatal(<-errs)
}

// sshServer returns an SSH server for the repositories under root, with the
// host key in the file hostKey, that accepts the keys in the file
// authorizedKeys.
func sshServer(root, hostKey, authorizedKeys string) (*gitserver.SSHServer, error) {
	if hostKey == "" || authorizedKeys == "" {
		return nil, errors.New("set -ssh-host-key and -ssh-authorized-keys with -ssh-addr")
	}
	b, err := os.ReadFile(hostKey)
	if err != nil {
		return nil, err
	}
	signer, err := ssh.ParsePrivateKey(b)
	if err != nil {
		return nil, fmt.Errorf("%s: %w", hostKey, err)
	}
	s := &gitserver.SSHServer{Root: root, HostKey: signer}
	rest, err := os.ReadFile(authorizedKeys)
	if err != nil {
		return nil, err
	}
	for len(bytes.TrimSpace(rest)) > 0 {
		var key ssh.PublicKey
		if key, _, _, rest, err = ssh.ParseAuthorizedKey(rest); err != nil {
			return nil, fmt.Errorf("%s: %w", authorizedKeys, err)
		}
		s.AuthorizedKeys = append(s.AuthorizedKeys, key)
	}
	return s, nil
}
