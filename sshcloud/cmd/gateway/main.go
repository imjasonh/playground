// Command gateway is the public SSH entrypoint for SSH App Cloud.
package main

import (
	"context"
	"flag"
	"log"
	"os"
	"os/signal"
	"syscall"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/sshd"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func main() {
	addr := flag.String("listen", "127.0.0.1:2222", "SSH listen address")
	hostKeyPath := flag.String("host-key", "ssh_host_ed25519_key", "path to host private key (created if missing)")
	flag.Parse()

	signer, err := hostkey.LoadOrGenerate(*hostKeyPath)
	if err != nil {
		log.Fatalf("host key: %v", err)
	}

	hub := &gateway.Hub{
		Store:    store.NewMemory(),
		Sessions: session.NewRegistry(),
	}
	srv := &sshd.Server{
		Hub:     hub,
		HostKey: signer,
		Addr:    *addr,
		Logger:  log.Default(),
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	log.Printf("sshcloud gateway on %s — host key %s", *addr, ssh.FingerprintSHA256(signer.PublicKey()))
	log.Printf("try: ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null join@127.0.0.1")
	if err := srv.ListenAndServe(ctx); err != nil {
		log.Fatalf("serve: %v", err)
	}
}
