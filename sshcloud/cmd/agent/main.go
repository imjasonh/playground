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
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8080", "agent HTTP listen address")
	workDir := flag.String("work-dir", "/var/lib/sshcloud/agent", "instance work directory")
	fcBin := flag.String("firecracker", "firecracker", "firecracker binary")
	kernel := flag.String("kernel", "", "path to vmlinux")
	rootfsPath := flag.String("rootfs", "", "path to base ext4 rootfs (fortune)")
	caPub := flag.String("ca-pub", "", "platform user CA public key to inject")
	guestInit := flag.String("guestinit", "", "linux guest PID1 trampoline for OCI boots (default: guestinit beside this binary)")
	snapDir := flag.String("snap-dir", "", "local snapshot directory (default: <work-dir>/snapshots)")
	gcsBucket := flag.String("gcs-bucket", "", "GCS bucket for snapshots (overrides -snap-dir)")
	gcsPrefix := flag.String("gcs-prefix", "sshcloud/snaps", "GCS object key prefix")
	idle := flag.Duration("idle", 5*time.Minute, "idle time before snapshot-sleep (0=disable)")
	flag.Parse()

	if *kernel == "" || *rootfsPath == "" {
		log.Fatal("-kernel and -rootfs are required")
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
	mgr, err := agent.NewManager(agent.Config{
		WorkDir:        *workDir,
		FirecrackerBin: *fcBin,
		KernelPath:     *kernel,
		BaseRootfs:     *rootfsPath,
		CAPubPath:      *caPub,
		GuestInitPath:  guestInitPath,
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
		log.Printf("sshcloud agent on %s (idle=%s guestinit=%s)", *listen, idle.String(), guestInitPath)
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	<-ctx.Done()
	_ = srv.Close()
}
