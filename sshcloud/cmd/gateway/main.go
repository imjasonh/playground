// Command gateway is the public SSH entrypoint for SSH App Cloud.
package main

import (
	"context"
	"flag"
	"log"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/image"
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
	firestorePrefix := flag.String("firestore-prefix", "sshcloud", "Firestore collection prefix")
	drainTimeout := flag.Duration("drain-timeout", cutover.DefaultDrainTimeout, "deploy drain kick timeout")
	controlTokenFile := flag.String("control-token-file", "", "bearer token file sent to orchestrator/agent APIs")
	controlListen := flag.String("control-listen", "", "internal migration control HTTP address (empty disables)")
	allowedRegistries := flag.String("allowed-registries", "index.docker.io,docker.io,ghcr.io,*.pkg.dev", "comma-separated OCI registry hosts; supports *.suffix")
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
	controlToken, err := controlauth.LoadFile(*controlTokenFile)
	if err != nil {
		log.Fatalf("control token: %v", err)
	}
	if (*orchURL != "" || *agentURL != "") && controlToken == "" {
		log.Printf("WARNING: internal API authentication is disabled")
	}

	var st store.Store = store.NewMemory()
	if *firestoreProject != "" {
		fs, err := store.NewFirestoreWithPrefix(ctx, *firestoreProject, *firestorePrefix)
		if err != nil {
			log.Fatalf("firestore: %v", err)
		}
		defer fs.Close()
		st = fs
		log.Printf("store: firestore project %s", *firestoreProject)
	} else {
		log.Printf("store: in-memory")
	}

	sess := session.NewRegistry()
	hub := &gateway.Hub{
		Store:             st,
		Sessions:          sess,
		UserCA:            ca,
		AllowedRegistries: image.ParseRegistryAllowlist(*allowedRegistries),
	}

	var instances cutover.Instances
	switch {
	case *orchURL != "":
		oc := &backend.OrchestratorClient{BaseURL: *orchURL, Token: controlToken}
		hub.Dial = func(ctx context.Context, req gateway.DialRequest) (gateway.DialTarget, error) {
			target, err := oc.TargetTierContext(ctx, req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle)
			return gateway.DialTarget{Addr: target.Addr, SSHHostPublicKey: target.SSHHostPublicKey}, err
		}
		instances = oc
		log.Printf("backend: orchestrator at %s (placement-aware)", *orchURL)
	case *agentURL != "":
		ac := &backend.AgentClient{BaseURL: *agentURL, Token: controlToken}
		hub.Dial = func(ctx context.Context, req gateway.DialRequest) (gateway.DialTarget, error) {
			in, err := ac.EnsureTierContext(ctx, req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle)
			return gateway.DialTarget{Addr: in.Addr, SSHHostPublicKey: in.SSHHostPublicKey}, err
		}
		instances = backend.AgentControl{Client: ac}
		log.Printf("backend: firecracker agent at %s", *agentURL)
	case *fortuneBin != "":
		caPubPath := *caKeyPath + ".pub"
		if err := os.WriteFile(caPubPath, ca.PublicAuthorizedKey(), 0o644); err != nil {
			log.Fatalf("write CA pub: %v", err)
		}
		abs, err := filepath.Abs(*fortuneBin)
		if err != nil {
			log.Fatal(err)
		}
		lf := backend.NewLocalFortune(abs, caPubPath)
		defer lf.Stop()
		hub.Dial = func(_ context.Context, req gateway.DialRequest) (gateway.DialTarget, error) {
			addr, hostKey, err := lf.Target(req.User, req.App, req.Gen, req.Image)
			return gateway.DialTarget{Addr: addr, SSHHostPublicKey: hostKey}, err
		}
		log.Printf("backend: local fortune process %s", abs)
	default:
		log.Printf("backend: in-process fortune stub")
	}

	if instances != nil {
		ctrl := cutover.New(st, sess, instances)
		ctrl.Timeout = *drainTimeout
		hub.Cutover = ctrl
		log.Printf("cutover: drain-timeout=%s", drainTimeout.String())
		go func() {
			reconcile := func() {
				reconcileCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
				defer cancel()
				if err := ctrl.Reconcile(reconcileCtx); err != nil && reconcileCtx.Err() == nil {
					log.Printf("cutover reconcile: %v", err)
				}
			}
			reconcile()
			ticker := time.NewTicker(30 * time.Second)
			defer ticker.Stop()
			for {
				select {
				case <-ctx.Done():
					return
				case <-ticker.C:
					reconcile()
				}
			}
		}()
	} else {
		log.Printf("cutover: disabled (no instance backend)")
	}

	srv := &sshd.Server{
		Hub:     hub,
		HostKey: signer,
		Addr:    *addr,
		Logger:  log.Default(),
	}

	var controlServer *http.Server
	if *controlListen != "" {
		controlMux := http.NewServeMux()
		(&gateway.ControlHandler{Hub: hub, Token: controlToken}).Mount(controlMux)
		controlServer = &http.Server{
			Addr: *controlListen, Handler: controlMux,
			ReadHeaderTimeout: 10 * time.Second, ReadTimeout: 30 * time.Second,
			WriteTimeout: 45 * time.Second, IdleTimeout: 60 * time.Second,
		}
		go func() {
			log.Printf("gateway migration control on %s", *controlListen)
			if err := controlServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
				log.Printf("migration control server: %v", err)
				stop()
			}
		}()
	}

	log.Printf("sshcloud gateway on %s — host key %s", *addr, ssh.FingerprintSHA256(signer.PublicKey()))
	log.Printf("user CA %s", ssh.FingerprintSHA256(ca.PublicKey()))
	log.Printf("try: ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null join@127.0.0.1")
	if err := srv.ListenAndServe(ctx); err != nil {
		log.Fatalf("serve: %v", err)
	}
	if controlServer != nil {
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		_ = controlServer.Shutdown(shutdownCtx)
	}
}
