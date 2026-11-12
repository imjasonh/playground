// Command casfs-csi is the CSI driver that mounts casfs inputs volumes for
// Substrate actors on the node it runs on. It runs as a DaemonSet on the
// worker nodes beside cascache, serves the CSI Node service on a unix socket
// in the kubelet plugins directory for atelet, and the Controller and
// Identity services on TCP for ateapi. Each volume it publishes is a casfs
// inputs volume for one tenant's instance, fetched from the node-local
// cascache with that tenant's token, so an actor's inputs come from its own
// node and the sandbox holds no credential.
package main

import (
	"context"
	"errors"
	"log/slog"
	"net"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"

	"github.com/sethvargo/go-envconfig"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/health"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"

	"github.com/imjasonh/playground/ci-substrate/internal/csidriver"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

type config struct {
	// Socket is the unix socket atelet dials for the Node service:
	// /var/lib/kubelet/plugins/<driver>/csi.sock on the host, mounted into
	// the pod.
	Socket string `env:"CSI_SOCKET, default=/csi/csi.sock"`
	// ControllerAddr is the TCP address ateapi dials for the Controller
	// service, through the driver's Service.
	ControllerAddr string `env:"CONTROLLER_ADDR, default=:9095"`
	// CacheAddr is the node-local cascache that volumes read from.
	CacheAddr string `env:"CACHE_ADDR, required"`
	// NodeID is the node's name, from the downward API.
	NodeID string `env:"NODE_ID, required"`
	// Tenants is the JSON tenant table that cas and cascache read: tokens to
	// instance names. The driver fetches as the tenant whose instance a
	// volume's StorageClass names.
	Tenants string `env:"TENANTS, required"`
}

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()
	var c config
	envconfig.MustProcess(ctx, &c)

	tenants, err := tenant.LoadJSON([]byte(c.Tenants))
	if err != nil {
		slog.Error("parsing tenants", "err", err)
		os.Exit(1)
	}
	conn, err := grpc.NewClient(c.CacheAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		slog.Error("dialing cache", "addr", c.CacheAddr, "err", err)
		os.Exit(1)
	}
	defer conn.Close()

	driver, err := csidriver.New(csidriver.Config{NodeID: c.NodeID, Fetcher: remote.NewClient(conn), Tenants: tenants})
	if err != nil {
		slog.Error("configuring driver", "err", err)
		os.Exit(1)
	}
	srv := grpc.NewServer()
	driver.Register(srv)
	hs := health.NewServer()
	hs.SetServingStatus("", healthpb.HealthCheckResponse_SERVING)
	healthpb.RegisterHealthServer(srv, hs)

	if err := os.MkdirAll(filepath.Dir(c.Socket), 0o755); err != nil {
		slog.Error("creating socket directory", "dir", filepath.Dir(c.Socket), "err", err)
		os.Exit(1)
	}
	// A socket left by an earlier process would refuse the listen.
	if err := os.Remove(c.Socket); err != nil && !errors.Is(err, os.ErrNotExist) {
		slog.Error("removing stale socket", "path", c.Socket, "err", err)
		os.Exit(1)
	}
	unixLis, err := net.Listen("unix", c.Socket)
	if err != nil {
		slog.Error("listen", "socket", c.Socket, "err", err)
		os.Exit(1)
	}
	tcpLis, err := net.Listen("tcp", c.ControllerAddr)
	if err != nil {
		slog.Error("listen", "addr", c.ControllerAddr, "err", err)
		os.Exit(1)
	}
	slog.Info("casfs-csi serving", "driver", csidriver.DriverName, "node", c.NodeID, "socket", c.Socket, "controller", c.ControllerAddr, "cache", c.CacheAddr)

	errc := make(chan error, 2)
	go func() { errc <- srv.Serve(unixLis) }()
	go func() { errc <- srv.Serve(tcpLis) }()
	select {
	case <-ctx.Done():
		slog.Info("shutting down")
	case err := <-errc:
		slog.Error("serve", "err", err)
	}
	hs.Shutdown()
	srv.GracefulStop()
	// A mount this process leaves behind would hang the sandbox that reads
	// it, so drop them all; atelet publishes again when the actor resumes.
	if err := driver.Close(); err != nil {
		slog.Error("unmounting volumes", "err", err)
		os.Exit(1)
	}
}
