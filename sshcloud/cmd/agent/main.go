// Command agent runs on each GCE host and manages Firecracker microVMs.
//
// Idle instances are snapshotted to -snap-dir (or -gcs-bucket) and restored on
// the next Ensure / POST /v1/instances/wake.
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
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8080", "agent control HTTPS listen address")
	healthListen := flag.String("health-listen", "127.0.0.1:8081", "unauthenticated health-only HTTP listen address")
	workDir := flag.String("work-dir", "/var/lib/sshcloud/agent", "instance work directory")
	fcBin := flag.String("firecracker", "firecracker", "Firecracker binary (explicit direct-runtime test mode only)")
	kernel := flag.String("kernel", "", "path to vmlinux")
	directRuntime := flag.Bool("direct-runtime", false, "launch Firecracker/TAP directly (local/KVM tests only; never production)")
	vmmHelperSocket := flag.String("vmm-helper-socket", "/run/sshcloud/vmmhelper.sock", "production VMM helper socket")
	tapHelperSocket := flag.String("tap-helper-socket", "/run/sshcloud/taphelper.sock", "production TAP helper socket")
	rootfsPath := flag.String("rootfs", "", "optional base ext4 for Ensure without image (test/dev only)")
	bootSpec := flag.String("boot-spec", "", "PID 1 spec JSON for -rootfs (default: sibling .boot.json)")
	caPub := flag.String("ca-pub", "", "platform user CA public key to inject")
	guestInit := flag.String("guestinit", "", "linux guest PID1 trampoline (default: guestinit beside this binary)")
	snapDir := flag.String("snap-dir", "", "local snapshot directory (default: <work-dir>/snapshots)")
	gcsBucket := flag.String("gcs-bucket", "", "GCS bucket for snapshots (overrides -snap-dir)")
	gcsPrefix := flag.String("gcs-prefix", "sshcloud/snaps", "GCS object key prefix")
	idle := flag.Duration("idle", 5*time.Minute, "idle time before snapshot-sleep (0=disable)")
	controlCert := flag.String("control-cert", "", "reloadable agent control certificate PEM")
	controlKey := flag.String("control-key", "", "reloadable agent control private-key PEM")
	controlCACurrent := flag.String("control-ca-current", "", "reloadable current control CA PEM")
	controlCAPrevious := flag.String("control-ca-previous", "", "reloadable previous control CA PEM")
	controlProjectID := flag.String("control-project-id", "", "expected GCE identity-token project ID")
	controlProjectNumber := flag.String("control-project-number", "", "expected GCE identity-token project number")
	orchestratorServiceAccount := flag.String("orchestrator-service-account", "", "exact orchestrator service-account email")
	insecureControl := flag.Bool("control-insecure-loopback", false, "explicitly allow unauthenticated plaintext control traffic on loopback only")
	relayHost := flag.String("relay-host", "", "agent VPC IP for gateway-reachable guest SSH relays (empty returns TAP-local addresses)")
	relayPortMin := flag.Int("relay-port-min", 20000, "first TCP port available for guest SSH relays")
	relayPortMax := flag.Int("relay-port-max", 29999, "last TCP port available for guest SSH relays")
	allowedRegistries := flag.String("allowed-registries", "index.docker.io,docker.io,ghcr.io,*.pkg.dev", "comma-separated OCI registry hosts; supports *.suffix")
	capacityVCPUs := flag.Int64("capacity-vcpus", 0, "allocatable guest vCPUs (0 detects host CPUs)")
	capacityMemMiB := flag.Int64("capacity-mem-mib", 0, "allocatable guest memory MiB (0 detects host memory minus 1 GiB)")
	platformVersion := flag.String("platform-version", "", "kernel/Firecracker compatibility ID stored in snapshots")
	cpuTemplate := flag.String("cpu-template", "", "portable Firecracker CPU template (production: T2)")
	flag.Parse()

	var vmRuntime agent.Runtime
	if *directRuntime {
		if *kernel == "" {
			log.Fatal("-kernel is required with -direct-runtime")
		}
		log.Printf("WARNING: direct Firecracker runtime enabled; local/KVM test mode only")
		vmRuntime = agent.DirectRuntime{}
	} else {
		vmRuntime = agent.NewHelperRuntime(*vmmHelperSocket, *tapHelperSocket)
	}
	controlFiles := controlauth.TLSFiles{
		CertFile: *controlCert, KeyFile: *controlKey,
		CurrentCAFile: *controlCACurrent, PreviousCAFile: *controlCAPrevious,
	}
	if *insecureControl {
		if err := controlauth.ValidateLoopbackListen(*listen); err != nil {
			log.Fatal(err)
		}
		log.Printf("WARNING: agent control uses explicit loopback-only insecure mode")
	} else if *controlProjectID == "" || *controlProjectNumber == "" || *orchestratorServiceAccount == "" {
		log.Fatal("production control requires -control-project-id, -control-project-number, and -orchestrator-service-account")
	}

	var store snapshot.Store
	switch {
	case *gcsBucket != "":
		s, err := snapshot.NewGCSStore(context.Background(), *gcsBucket, *gcsPrefix)
		if err != nil {
			log.Fatalf("gcs store: %v", err)
		}
		defer s.Close()
		store = s
		log.Printf("snapshot store: gs://%s/%s", *gcsBucket, *gcsPrefix)
	default:
		dir := *snapDir
		if dir == "" {
			dir = filepath.Join(*workDir, "snapshots")
		}
		s, err := snapshot.NewLocalStore(dir)
		if err != nil {
			log.Fatal(err)
		}
		store = s
		log.Printf("snapshot store: %s", dir)
	}

	ociCache := filepath.Join(*workDir, "oci-rootfs")
	guestInitPath := strings.TrimSpace(*guestInit)
	if guestInitPath == "" {
		if exe, err := os.Executable(); err == nil {
			cand := filepath.Join(filepath.Dir(exe), "guestinit")
			if st, err := os.Stat(cand); err == nil && st.Mode().IsRegular() {
				guestInitPath = cand
			}
		}
	}
	if guestInitPath == "" {
		log.Fatal("-guestinit is required (linux guest PID 1 trampoline)")
	}
	if st, err := os.Stat(guestInitPath); err != nil || !st.Mode().IsRegular() {
		log.Fatalf("guestinit %s: %v", guestInitPath, err)
	}

	var baseSpec guestinit.Spec
	bootSpecPath := strings.TrimSpace(*bootSpec)
	baseRootfs := strings.TrimSpace(*rootfsPath)
	if baseRootfs != "" {
		if bootSpecPath == "" {
			bootSpecPath = guestinit.SpecBeside(baseRootfs)
		}
		spec, err := guestinit.LoadFile(bootSpecPath)
		if err != nil {
			log.Fatalf("boot spec %s: %v", bootSpecPath, err)
		}
		if err := spec.Validate(); err != nil {
			log.Fatalf("boot spec %s: %v", bootSpecPath, err)
		}
		baseSpec = spec
	}

	mgr, err := agent.NewManager(agent.Config{
		WorkDir:           *workDir,
		FirecrackerBin:    *fcBin,
		KernelPath:        *kernel,
		BaseRootfs:        baseRootfs,
		CAPubPath:         *caPub,
		GuestInitPath:     guestInitPath,
		BaseBootSpec:      baseSpec,
		RelayHost:         strings.TrimSpace(*relayHost),
		RelayPortMin:      *relayPortMin,
		RelayPortMax:      *relayPortMax,
		AllowedRegistries: image.ParseRegistryAllowlist(*allowedRegistries),
		CapacityVCPUs:     *capacityVCPUs,
		CapacityMemMiB:    *capacityMemMiB,
		PlatformVersion:   strings.TrimSpace(*platformVersion),
		CPUTemplate:       strings.TrimSpace(*cpuTemplate),
		Runtime:           vmRuntime,
		SnapStore:         store,
		IdleTimeout:       *idle,
		RootfsResolver: func(ctx context.Context, imageRef string) (agent.ResolvedRootfs, error) {
			res, err := ocirootfs.Materialize(ctx, imageRef, ocirootfs.Options{CacheDir: ociCache})
			if err != nil {
				return agent.ResolvedRootfs{}, err
			}
			return agent.ResolvedRootfs{Path: res.Rootfs, Spec: res.Spec}, nil
		},
	})
	if err != nil {
		log.Fatal(err)
	}
	controlMux := http.NewServeMux()
	handler := &agent.Handler{Manager: mgr, Readiness: mgr.Ready}
	handler.Mount(controlMux)
	var controlHandler http.Handler = controlMux
	var tlsConfig *tls.Config
	if !*insecureControl {
		verifier := &controlauth.GCEVerifier{
			ProjectID: *controlProjectID, ProjectNumber: *controlProjectNumber,
		}
		controlHandler = controlauth.Require(verifier, controlauth.VerificationPolicy{
			CallerRole: controlauth.RoleOrchestrator, ServiceAccount: *orchestratorServiceAccount,
			Audience: controlauth.AudienceAgent,
		}, controlMux)
		tlsConfig, err = controlauth.ServerTLSConfig(controlFiles, controlauth.RoleAgent)
		if err != nil {
			log.Fatalf("agent control TLS: %v", err)
		}
	}

	srv := &http.Server{
		Addr:              *listen,
		Handler:           controlHandler,
		ReadHeaderTimeout: 10 * time.Second,
		ReadTimeout:       30 * time.Second,
		WriteTimeout:      6 * time.Minute,
		IdleTimeout:       60 * time.Second,
	}
	listener, err := net.Listen("tcp", *listen)
	if err != nil {
		log.Fatalf("agent control listen: %v", err)
	}
	if tlsConfig != nil {
		listener = tls.NewListener(listener, tlsConfig)
	}
	go func() {
		log.Printf("sshcloud agent on %s (idle=%s guestinit=%s base-rootfs=%q)", *listen, idle.String(), guestInitPath, baseRootfs)
		if err := srv.Serve(listener); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()
	var healthServer *http.Server
	if *healthListen != "" {
		healthMux := http.NewServeMux()
		handler.MountHealth(healthMux)
		healthServer = &http.Server{
			Addr: *healthListen, Handler: healthMux,
			ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 5 * time.Second,
			WriteTimeout: 5 * time.Second, IdleTimeout: 30 * time.Second,
		}
		go func() {
			log.Printf("sshcloud agent health HTTP on %s", *healthListen)
			if err := healthServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
				log.Fatal(err)
			}
		}()
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	<-ctx.Done()
	shutdownCtx, cancelShutdown := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancelShutdown()
	_ = srv.Shutdown(shutdownCtx)
	if healthServer != nil {
		_ = healthServer.Shutdown(shutdownCtx)
	}
	if err := mgr.Close(); err != nil {
		log.Fatalf("agent shutdown could not durably snapshot all instances: %v", err)
	}
}
