// Command agent runs on each GCE host and manages Firecracker microVMs.
//
// Idle instances are snapshotted to -snap-dir (or -gcs-bucket) and restored on
// the next Ensure / POST /v1/instances/wake.
package main

import (
	"context"
	"flag"
	"log"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8080", "agent HTTP listen address")
	workDir := flag.String("work-dir", "/var/lib/sshcloud/agent", "instance work directory")
	fcBin := flag.String("firecracker", "firecracker", "firecracker binary")
	kernel := flag.String("kernel", "", "path to vmlinux")
	rootfsPath := flag.String("rootfs", "", "optional base ext4 for Ensure without image (test/dev only)")
	bootSpec := flag.String("boot-spec", "", "PID 1 spec JSON for -rootfs (default: sibling .boot.json)")
	caPub := flag.String("ca-pub", "", "platform user CA public key to inject")
	guestInit := flag.String("guestinit", "", "linux guest PID1 trampoline (default: guestinit beside this binary)")
	snapDir := flag.String("snap-dir", "", "local snapshot directory (default: <work-dir>/snapshots)")
	gcsBucket := flag.String("gcs-bucket", "", "GCS bucket for snapshots (overrides -snap-dir)")
	gcsPrefix := flag.String("gcs-prefix", "sshcloud/snaps", "GCS object key prefix")
	idle := flag.Duration("idle", 5*time.Minute, "idle time before snapshot-sleep (0=disable)")
	flag.Parse()

	if *kernel == "" {
		log.Fatal("-kernel is required")
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
		WorkDir:        *workDir,
		FirecrackerBin: *fcBin,
		KernelPath:     *kernel,
		BaseRootfs:     baseRootfs,
		CAPubPath:      *caPub,
		GuestInitPath:  guestInitPath,
		BaseBootSpec:   baseSpec,
		SnapStore:      store,
		IdleTimeout:    *idle,
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
	defer mgr.Close()

	mux := http.NewServeMux()
	(&agent.Handler{Manager: mgr}).Mount(mux)

	srv := &http.Server{Addr: *listen, Handler: mux, ReadHeaderTimeout: 10 * time.Second}
	go func() {
		log.Printf("sshcloud agent on %s (idle=%s guestinit=%s base-rootfs=%q)", *listen, idle.String(), guestInitPath, baseRootfs)
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	<-ctx.Done()
	_ = srv.Close()
}
