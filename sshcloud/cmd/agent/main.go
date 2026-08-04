// Command agent runs on each GCE host and manages Firecracker microVMs.
package main

import (
	"context"
	"flag"
	"log"
	"net/http"
	"os"
	"os/signal"
	"syscall"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:8080", "agent HTTP listen address")
	workDir := flag.String("work-dir", "/var/lib/sshcloud/agent", "instance work directory")
	fcBin := flag.String("firecracker", "firecracker", "firecracker binary")
	kernel := flag.String("kernel", "", "path to vmlinux")
	rootfsPath := flag.String("rootfs", "", "path to base ext4 rootfs (fortune)")
	caPub := flag.String("ca-pub", "", "platform user CA public key to inject")
	flag.Parse()

	if *kernel == "" || *rootfsPath == "" {
		log.Fatal("-kernel and -rootfs are required")
	}

	mgr, err := agent.NewManager(agent.Config{
		WorkDir:        *workDir,
		FirecrackerBin: *fcBin,
		KernelPath:     *kernel,
		BaseRootfs:     *rootfsPath,
		CAPubPath:      *caPub,
	})
	if err != nil {
		log.Fatal(err)
	}
	defer mgr.Close()

	mux := http.NewServeMux()
	(&agent.Handler{Manager: mgr}).Mount(mux)

	srv := &http.Server{Addr: *listen, Handler: mux}
	go func() {
		log.Printf("sshcloud agent on %s", *listen)
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	<-ctx.Done()
	_ = srv.Close()
}
