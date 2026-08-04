// Command gateway is the public SSH entrypoint for SSH App Cloud.
package main

import (
	"context"
	"flag"
	"log"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/sshd"
	"github.com/imjasonh/playground/sshcloud/internal/store"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

func main() {
	addr := flag.String("listen", "127.0.0.1:2222", "SSH listen address")
	hostKeyPath := flag.String("host-key", "ssh_host_ed25519_key", "path to host private key (created if missing)")
	caKeyPath := flag.String("user-ca", "ssh_user_ca", "path to user CA private key (created if missing)")
	fortuneBin := flag.String("fortune-bin", "", "path to local fortune binary (process backend)")
	agentURL := flag.String("agent-url", "", "host agent base URL (Firecracker backend), e.g. http://127.0.0.1:8080")
	orchURL := flag.String("orchestrator-url", "", "orchestrator base URL (placement-aware Ensure), e.g. http://127.0.0.1:8090")
	firestoreProject := flag.String("firestore-project", "", "GCP project for Firestore user/app store (default: in-memory)")
	flag.Parse()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	signer, err := hostkey.LoadOrGenerate(*hostKeyPath)
	if err != nil {
		log.Fatalf("host key: %v", err)
	}
	ca, err := userca.LoadOrGenerate(*caKeyPath)
	if err != nil {
		log.Fatalf("user CA: %v", err)
	}
	caPubPath := *caKeyPath + ".pub"
	if err := os.WriteFile(caPubPath, ca.PublicAuthorizedKey(), 0o644); err != nil {
		log.Fatalf("write CA pub: %v", err)
	}

	var st store.Store = store.NewMemory()
	if *firestoreProject != "" {
		fs, err := store.NewFirestore(ctx, *firestoreProject)
		if err != nil {
			log.Fatalf("firestore: %v", err)
		}
		defer fs.Close()
		st = fs
		log.Printf("store: firestore project %s", *firestoreProject)
	} else {
		log.Printf("store: in-memory")
	}

	hub := &gateway.Hub{
		Store:    st,
		Sessions: session.NewRegistry(),
		UserCA:   ca,
	}
	switch {
	case *orchURL != "":
		hub.Dial = (&backend.OrchestratorClient{BaseURL: *orchURL}).Addr
		log.Printf("backend: orchestrator at %s (placement-aware)", *orchURL)
	case *agentURL != "":
		hub.Dial = (&backend.AgentClient{BaseURL: *agentURL}).Addr
		log.Printf("backend: firecracker agent at %s", *agentURL)
	case *fortuneBin != "":
		abs, err := filepath.Abs(*fortuneBin)
		if err != nil {
			log.Fatal(err)
		}
		lf := backend.NewLocalFortune(abs, caPubPath)
		defer lf.Stop()
		hub.Dial = lf.Addr
		log.Printf("backend: local fortune process %s", abs)
	default:
		log.Printf("backend: in-process fortune stub")
	}

	srv := &sshd.Server{
		Hub:     hub,
		HostKey: signer,
		Addr:    *addr,
		Logger:  log.Default(),
	}

	log.Printf("sshcloud gateway on %s — host key %s", *addr, ssh.FingerprintSHA256(signer.PublicKey()))
	log.Printf("user CA %s", ssh.FingerprintSHA256(ca.PublicKey()))
	log.Printf("try: ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null join@127.0.0.1")
	if err := srv.ListenAndServe(ctx); err != nil {
		log.Fatalf("serve: %v", err)
	}
}
