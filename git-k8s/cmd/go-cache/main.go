// Command go-cache serves a Go module proxy and Go build caches to
// check-gotest's test Pods.
//
// The module proxy, at /mod/, fetches modules from an upstream proxy and
// keeps the files of canonical versions, which never change, so test Pods
// download modules without reaching the internet.
//
// A build cache, at /cache/NAMESPACE/REPOSITORY/, holds the outputs of the
// go command's build steps for one GitRepository, by action ID. Reading or
// writing it takes a service account token from the repository's namespace
// with an audience that grants that access, which go-cache checks with a
// TokenReview. check-gotest gives the token that reads to the container
// that compiles a branch, and the token that writes to a container that
// uploads what the compiler built, before any of the branch's code runs.
// go-cache accepts a token that writes only if the token is bound to a Pod
// that check-gotest owns and that is Pending. The container that uploads
// is an init container, which runs while its Pod is Pending. Set
// -controller if check-gotest runs under another name.
//
// go-cache keeps modules and outputs in -dir, and keeps them, with the
// writes in progress, under -max-size. A write reserves room for its bytes
// before it writes them, and go-cache removes the least recently used
// files to make room. Uploads and module fetches have separate slots for
// their writes. When writes in progress hold the room, or every slot that
// a new write needs, go-cache answers an upload with 503, and serves a
// module from the upstream without keeping it.
package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"math"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/kube"
	"golang.org/x/sync/singleflight"
)

type server struct {
	store    *store
	upstream string
	client   *http.Client
	// reviewer is nil outside a cluster, which turns the build caches off.
	reviewer reviewer
	metrics  *metrics
	log      *slog.Logger
	// fetches holds the module fetches in progress, by key.
	fetches singleflight.Group
}

func (s *server) handler() http.Handler {
	mux := s.health()
	mux.HandleFunc("GET /mod/", s.module)
	mux.HandleFunc("GET /cache/{namespace}/{repository}/{action}", s.getOutput)
	mux.HandleFunc("PUT /cache/{namespace}/{repository}/{action}", s.putOutput)
	return mux
}

// health returns a mux that serves /healthz, /readyz, and /metrics.
func (s *server) health() *http.ServeMux {
	mux := http.NewServeMux()
	ok := func(w http.ResponseWriter, _ *http.Request) { fmt.Fprintln(w, "ok") }
	mux.HandleFunc("GET /healthz", ok)
	mux.HandleFunc("GET /readyz", ok)
	mux.HandleFunc("GET /metrics", s.metrics.serve)
	return mux
}

// servers returns the servers for -addr and, if it's another address,
// -metrics-addr.
func (s *server) servers(addr, metricsAddr string) []*http.Server {
	servers := []*http.Server{{
		Addr:              addr,
		Handler:           s.handler(),
		ReadHeaderTimeout: 10 * time.Second,
		// ReadTimeout limits how long a slow upload holds a write and its
		// room in the store.
		ReadTimeout: 5 * time.Minute,
		IdleTimeout: 2 * time.Minute,
	}}
	if metricsAddr != "" && metricsAddr != addr {
		servers = append(servers, &http.Server{Addr: metricsAddr, Handler: s.health(), ReadHeaderTimeout: 10 * time.Second})
	}
	return servers
}

// parseSize parses a number of bytes with an optional suffix, as in a
// Kubernetes quantity such as 512Mi or 8G.
func parseSize(s string) (int64, error) {
	n, mult := s, int64(1)
	for _, u := range []struct {
		suffix string
		mult   int64
	}{
		{"Ki", 1 << 10}, {"Mi", 1 << 20}, {"Gi", 1 << 30}, {"Ti", 1 << 40},
		{"k", 1e3}, {"M", 1e6}, {"G", 1e9}, {"T", 1e12},
	} {
		if rest, ok := strings.CutSuffix(s, u.suffix); ok {
			n, mult = rest, u.mult
			break
		}
	}
	v, err := strconv.ParseInt(n, 10, 64)
	if err != nil || v <= 0 || v > math.MaxInt64/mult {
		return 0, fmt.Errorf("%q isn't a size, such as 512Mi or 8Gi", s)
	}
	return v * mult, nil
}

func main() {
	upstream := flag.String("upstream", "https://proxy.golang.org", "module proxy to fetch modules from")
	dir := flag.String("dir", filepath.Join(os.TempDir(), "go-cache"), "directory to keep modules and build outputs in")
	maxSize := flag.String("max-size", "4Gi", "most bytes that files in -dir and writes in progress can take, such as 512Mi or 8Gi; keep it below the size of -dir's volume")
	controller := flag.String("controller", "check-gotest", "kube controller whose Pods may write to the build caches")
	if len(os.Args) > 1 && os.Args[1] == "generate" {
		// go-cache has no controllers, but generate installs it like a
		// controller program, and the Deployment passes kube.Main's
		// -metrics-addr for its probes. generate fails on a program that
		// defines that flag itself, so go-cache defines its serving flags
		// only when it serves.
		kube.Main()
		return
	}
	addr := flag.String("addr", ":8080", "address to serve the module proxy and the build caches on")
	metricsAddr := flag.String("metrics-addr", "", "address for /healthz, /readyz, and /metrics, if not -addr")
	flag.Parse()
	log := slog.New(slog.NewTextHandler(os.Stderr, nil))
	if err := run(log, *addr, *metricsAddr, *upstream, *dir, *maxSize, *controller); err != nil {
		log.Error("exiting", "err", err)
		os.Exit(1)
	}
}

func run(log *slog.Logger, addr, metricsAddr, upstream, dir, maxSize, controller string) error {
	max, err := parseSize(maxSize)
	if err != nil {
		return fmt.Errorf("-max-size: %w", err)
	}
	if u, err := url.Parse(upstream); err != nil || (u.Scheme != "http" && u.Scheme != "https") || u.Host == "" {
		return fmt.Errorf("-upstream %q isn't an http or https URL", upstream)
	}
	if controller == "" {
		return errors.New("-controller can't be empty")
	}
	m := newMetrics()
	st, err := openStore(dir, max, m, log)
	if err != nil {
		return err
	}
	s := &server{
		store:    st,
		upstream: strings.TrimSuffix(upstream, "/"),
		client:   &http.Client{Timeout: 10 * time.Minute},
		metrics:  m,
		log:      log,
	}
	if r, err := inCluster(controller); err != nil {
		log.Warn("the build caches are off, because go-cache can't review tokens outside a cluster", "err", err)
	} else {
		s.reviewer = r
	}
	servers := s.servers(addr, metricsAddr)
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	log.Info("serving", "addr", addr, "metrics-addr", metricsAddr, "upstream", upstream, "dir", dir, "max-size", maxSize, "controller", controller)
	errc := make(chan error, len(servers))
	for _, srv := range servers {
		go func() { errc <- srv.ListenAndServe() }()
	}
	select {
	case err := <-errc:
		return err
	case <-ctx.Done():
	}
	shutdown, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	var errs []error
	for _, srv := range servers {
		errs = append(errs, srv.Shutdown(shutdown))
	}
	return errors.Join(errs...)
}
