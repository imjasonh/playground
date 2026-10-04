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
//
// go-cache keeps modules and outputs in -dir, and removes the least
// recently used files when they pass -max-size.
package main

import (
	"context"
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
)

type server struct {
	store    *store
	upstream string
	client   *http.Client
	// reviewer is nil outside a cluster, which turns the build caches off.
	reviewer reviewer
	metrics  *metrics
	log      *slog.Logger
}

func (s *server) handler() http.Handler {
	mux := http.NewServeMux()
	ok := func(w http.ResponseWriter, _ *http.Request) { fmt.Fprintln(w, "ok") }
	mux.HandleFunc("GET /healthz", ok)
	mux.HandleFunc("GET /readyz", ok)
	mux.HandleFunc("GET /metrics", s.metrics.serve)
	mux.HandleFunc("GET /mod/", s.module)
	mux.HandleFunc("GET /cache/{namespace}/{repository}/{action}", s.getOutput)
	mux.HandleFunc("PUT /cache/{namespace}/{repository}/{action}", s.putOutput)
	return mux
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
	if len(os.Args) > 1 && os.Args[1] == "generate" {
		// go-cache has no controllers, but generate installs it like a
		// controller program.
		kube.Main()
		return
	}
	addr := flag.String("addr", ":8080", "address to serve on")
	upstream := flag.String("upstream", "https://proxy.golang.org", "module proxy to fetch modules from")
	dir := flag.String("dir", filepath.Join(os.TempDir(), "go-cache"), "directory to keep modules and build outputs in")
	maxSize := flag.String("max-size", "4Gi", "most bytes to keep in -dir, such as 512Mi or 8Gi; keep it below the size of -dir's volume")
	flag.Parse()
	log := slog.New(slog.NewTextHandler(os.Stderr, nil))
	if err := run(log, *addr, *upstream, *dir, *maxSize); err != nil {
		log.Error("exiting", "err", err)
		os.Exit(1)
	}
}

func run(log *slog.Logger, addr, upstream, dir, maxSize string) error {
	max, err := parseSize(maxSize)
	if err != nil {
		return fmt.Errorf("-max-size: %w", err)
	}
	if u, err := url.Parse(upstream); err != nil || (u.Scheme != "http" && u.Scheme != "https") || u.Host == "" {
		return fmt.Errorf("-upstream %q isn't an http or https URL", upstream)
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
	if r, err := inCluster(); err != nil {
		log.Warn("the build caches are off, because go-cache can't review tokens outside a cluster", "err", err)
	} else {
		s.reviewer = r
	}
	srv := &http.Server{Addr: addr, Handler: s.handler(), ReadHeaderTimeout: 10 * time.Second}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	log.Info("serving", "addr", addr, "upstream", upstream, "dir", dir, "max-size", maxSize)
	errc := make(chan error, 1)
	go func() { errc <- srv.ListenAndServe() }()
	select {
	case err := <-errc:
		return err
	case <-ctx.Done():
	}
	shutdown, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	return srv.Shutdown(shutdown)
}
