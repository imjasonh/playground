// Command gateway is the public SSH entrypoint for SSH App Cloud.
package main

import (
	"context"
	"crypto/tls"
	"flag"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/access"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/sshd"
	"github.com/imjasonh/playground/sshcloud/internal/store"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

func main() {
	observability.Configure("gateway")
	addr := flag.String("listen", "127.0.0.1:2222", "SSH listen address")
	hostKeyPath := flag.String("host-key", "ssh_host_ed25519_key", "path to host private key (created if missing)")
	caKeyPath := flag.String("user-ca", "ssh_user_ca", "path to user CA private key (created if missing)")
	fortuneBin := flag.String("fortune-bin", "", "path to local fortune binary (process backend)")
	agentURL := flag.String("agent-url", "", "local-only direct host-agent URL; requires -control-insecure-loopback")
	orchURL := flag.String("orchestrator-url", "", "orchestrator gateway-service HTTPS URL")
	firestoreProject := flag.String("firestore-project", "", "GCP project for Firestore user/app store (default: in-memory)")
	firestorePrefix := flag.String("firestore-prefix", "sshcloud", "Firestore collection prefix")
	userFirestoreDatabase := flag.String("user-firestore-database", "sshcloud-user", "user/app/quota Firestore database ID")
	drainTimeout := flag.Duration("drain-timeout", cutover.DefaultDrainTimeout, "deploy drain kick timeout")
	controlListen := flag.String("control-listen", "", "internal migration-control HTTPS address (empty disables)")
	healthListen := flag.String("health-listen", "", "unauthenticated health-only HTTP address (empty disables)")
	controlCert := flag.String("control-cert", "", "reloadable gateway control certificate PEM")
	controlKey := flag.String("control-key", "", "reloadable gateway control private-key PEM")
	controlCACurrent := flag.String("control-ca-current", "", "reloadable current control CA PEM")
	controlCAPrevious := flag.String("control-ca-previous", "", "reloadable previous control CA PEM")
	controlBundle := flag.String("control-bundle", "", "atomically switched control TLS bundle directory")
	controlBundleMaxAge := flag.Duration("control-bundle-max-age", controlauth.DefaultBundleLease, "last-known-good control bundle lease")
	controlProjectID := flag.String("control-project-id", "", "expected GCE identity-token project ID")
	controlProjectNumber := flag.String("control-project-number", "", "expected GCE identity-token project number")
	orchestratorServiceAccount := flag.String("orchestrator-service-account", "", "exact orchestrator service-account email")
	insecureControl := flag.Bool("control-insecure-loopback", false, "explicitly allow unauthenticated plaintext control traffic on loopback only")
	accessPolicyFile := flag.String("access-policy-file", "", "path to reloadable JSON SSH-key access policy (empty is local open/all-users)")
	accessPolicyMaxAge := flag.Duration("access-policy-max-age", 5*time.Minute, "last-known-good access policy lease")
	allowedRegistries := flag.String("allowed-registries", "index.docker.io,docker.io,ghcr.io,*.pkg.dev", "comma-separated OCI registry hosts; supports *.suffix")
	maxSessionsPerUser := flag.Int("max-sessions-per-user", 5, "concurrent sessions across all apps")
	handshakesPerMinute := flag.Int("handshakes-per-minute", 60, "accepted SSH handshakes per source IP per minute")
	maxAppsPerUser := flag.Int("max-apps-per-user", 5, "maximum apps per user")
	deploysPerHour := flag.Int("deploys-per-hour", 10, "deploy admissions per user per hour")
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
	controlFiles := controlauth.TLSFiles{
		BundleDir: *controlBundle,
		MaxAge:    *controlBundleMaxAge,
		CertFile:  *controlCert, KeyFile: *controlKey,
		CurrentCAFile: *controlCACurrent, PreviousCAFile: *controlCAPrevious,
	}
	controlEnabled := *orchURL != "" || *agentURL != "" || *controlListen != ""
	if *insecureControl {
		if *controlListen != "" {
			if err := controlauth.ValidateLoopbackListen(*controlListen); err != nil {
				log.Fatal(err)
			}
		}
		if *agentURL == "" && *orchURL == "" && *controlListen == "" {
			log.Printf("control: explicit loopback-insecure mode has no configured control endpoint")
		} else {
			log.Printf("WARNING: control plane uses explicit loopback-only insecure mode")
		}
	} else if controlEnabled {
		if *controlProjectID == "" || *controlProjectNumber == "" || *orchestratorServiceAccount == "" {
			log.Fatal("production control requires -control-project-id, -control-project-number, and -orchestrator-service-account")
		}
		if *agentURL != "" {
			log.Fatal("-agent-url is local-only: production agents authorize the orchestrator role, never gateway")
		}
	}

	var st store.Store = store.NewMemory()
	if *firestoreProject != "" {
		fs, err := store.NewFirestoreDatabase(ctx, *firestoreProject, *userFirestoreDatabase, *firestorePrefix)
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
	sess.MaxPerUser = *maxSessionsPerUser
	var accessPolicy access.Source = access.StaticSource{Policy: access.LocalDevelopmentPolicy()}
	if *accessPolicyFile != "" {
		filePolicy := access.FileSource{Path: *accessPolicyFile, MaxAge: *accessPolicyMaxAge}
		accessPolicy = filePolicy
		if _, err := filePolicy.Load(); err != nil {
			log.Fatalf("access policy must be valid before gateway start: %v", err)
		}
		log.Printf("access policy: reload %s on each admission (lease %s)", *accessPolicyFile, accessPolicyMaxAge.String())
	} else {
		log.Printf("access policy: local development open/all-users (no policy file configured)")
	}
	var quotaStore quota.Store = quota.NewMemory()
	if *firestoreProject != "" {
		quotaStore, err = quota.NewFirestoreDatabase(ctx, *firestoreProject, *userFirestoreDatabase, *firestorePrefix)
		if err != nil {
			log.Fatalf("quota firestore: %v", err)
		}
		defer quotaStore.Close()
	}
	hub := &gateway.Hub{
		Store:             st,
		Sessions:          sess,
		Access:            accessPolicy,
		UserCA:            ca,
		AllowedRegistries: image.ParseRegistryAllowlist(*allowedRegistries),
		Quotas:            quotaStore,
		Limits:            gateway.Limits{AppsPerUser: *maxAppsPerUser, DeploysPerHour: *deploysPerHour},
		RuntimeReady: func() error {
			return controlauth.BundleFresh(*controlBundle, *controlBundleMaxAge)
		},
	}

	var instances cutover.Instances
	switch {
	case *orchURL != "":
		oc := &backend.OrchestratorClient{BaseURL: *orchURL, InsecureLoopback: *insecureControl}
		if !*insecureControl {
			client, err := controlauth.NewClient(
				controlFiles, controlauth.RoleGateway, controlauth.RoleOrchestrator,
				controlauth.MetadataTokenSource{}, controlauth.AudienceOrchestratorGateway, 6*time.Minute,
			)
			if err != nil {
				log.Fatalf("orchestrator control client: %v", err)
			}
			oc.ControlClient = client
		}
		hub.Dial = func(ctx context.Context, req gateway.DialRequest) (gateway.DialTarget, error) {
			target, err := oc.TargetTierRequest(ctx, req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle, req.Purpose, req.RequestID)
			return gateway.DialTarget{Addr: target.Addr, SSHHostPublicKey: target.SSHHostPublicKey}, err
		}
		instances = oc
		hub.BackendReady = oc.Ready
		log.Printf("backend: orchestrator at %s (placement-aware)", *orchURL)
	case *agentURL != "":
		ac := &backend.AgentClient{BaseURL: *agentURL, InsecureLoopback: true}
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
		Hub:              hub,
		HostKey:          signer,
		Addr:             *addr,
		Logger:           log.Default(),
		HandshakeLimiter: quota.NewIPRateLimiter(*handshakesPerMinute, time.Minute),
	}

	controlHandler := &gateway.ControlHandler{Hub: hub}
	var controlServer, healthServer *http.Server
	if *controlListen != "" {
		controlMux := http.NewServeMux()
		controlHandler.Mount(controlMux)
		var handler http.Handler = controlMux
		var tlsConfig *tls.Config
		if !*insecureControl {
			verifier := &controlauth.GCEVerifier{
				ProjectID: *controlProjectID, ProjectNumber: *controlProjectNumber,
			}
			handler = controlauth.Require(verifier, controlauth.VerificationPolicy{
				CallerRole: controlauth.RoleOrchestrator, ServiceAccount: *orchestratorServiceAccount,
				Audience: controlauth.AudienceGatewayMigration,
			}, controlMux)
			var err error
			tlsConfig, err = controlauth.ServerTLSConfig(controlFiles, controlauth.RoleGateway)
			if err != nil {
				log.Fatalf("gateway control TLS: %v", err)
			}
		}
		controlServer = &http.Server{
			Addr: *controlListen, Handler: handler,
			ReadHeaderTimeout: 10 * time.Second, ReadTimeout: 30 * time.Second,
			WriteTimeout: 45 * time.Second, IdleTimeout: 60 * time.Second,
		}
		listener, err := net.Listen("tcp", *controlListen)
		if err != nil {
			log.Fatalf("gateway control listen: %v", err)
		}
		if tlsConfig != nil {
			listener = tls.NewListener(listener, tlsConfig)
		}
		go func() {
			log.Printf("gateway migration control on %s", *controlListen)
			if err := controlServer.Serve(listener); err != nil && err != http.ErrServerClosed {
				log.Printf("migration control server: %v", err)
				stop()
			}
		}()
	}
	if *healthListen != "" {
		healthMux := http.NewServeMux()
		controlHandler.MountHealth(healthMux)
		healthMux.Handle("GET /metrics", observability.MetricsHandler())
		healthServer = &http.Server{
			Addr: *healthListen, Handler: healthMux,
			ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 5 * time.Second,
			WriteTimeout: 5 * time.Second, IdleTimeout: 30 * time.Second,
		}
		go func() {
			log.Printf("gateway health HTTP on %s", *healthListen)
			if err := healthServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
				log.Printf("gateway health server: %v", err)
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
	if healthServer != nil {
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		_ = healthServer.Shutdown(shutdownCtx)
	}
}
