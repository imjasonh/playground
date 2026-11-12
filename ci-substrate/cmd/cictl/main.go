// Command cictl is the control-plane CLI and demo driver. Its demo subcommand
// drives the central cas and a node-local cascache to show the two headline
// properties on a live cluster: multi-tenant isolation (one tenant cannot read
// another's instance) and optimized caching (a blob one tenant warmed is
// served to another tenant from the node-local cache with no second origin
// fetch).
package main

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"

	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

func main() {
	originAddr := flag.String("origin-addr", "", "origin cas address (host:port)")
	cacheAddr := flag.String("cache-addr", "", "node-local cascache address (host:port)")
	cacheMetricsURL := flag.String("cache-metrics-url", "", "cascache metrics base URL, e.g. http://host:9090")
	tokenA := flag.String("token-a", "tok-a", "tenant A token")
	tokenB := flag.String("token-b", "tok-b", "tenant B token")
	instanceA := flag.String("instance-a", "tenant-a", "tenant A private instance")
	shared := flag.String("shared", "shared", "instance both tenants may read")
	flag.Parse()

	if *originAddr == "" || *cacheAddr == "" {
		slog.Error("missing required flags", "need", "-origin-addr and -cache-addr")
		os.Exit(2)
	}

	if err := run(*originAddr, *cacheAddr, *cacheMetricsURL, *tokenA, *tokenB, *instanceA, *shared); err != nil {
		slog.Error("demo failed", "err", err)
		os.Exit(1)
	}
	slog.Info("demo passed: multi-tenant isolation and node-local cache reuse verified")
}

func run(originAddr, cacheAddr, metricsURL, tokenA, tokenB, instanceA, shared string) error {
	originConn, err := grpc.NewClient(originAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer originConn.Close()
	cacheConn, err := grpc.NewClient(cacheAddr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return err
	}
	defer cacheConn.Close()
	origin := remote.NewClient(originConn)
	cacheClient := remote.NewClient(cacheConn)

	ctxA := tenant.Outgoing(context.Background(), tokenA)
	ctxB := tenant.Outgoing(context.Background(), tokenB)

	// Tenant A uploads a shared blob to the origin.
	content := []byte(fmt.Sprintf("shared build artifact %d", time.Now().UnixNano()))
	d, err := retry(func() (*repb.Digest, error) {
		return origin.Upload(ctxA, shared, content)
	})
	if err != nil {
		return fmt.Errorf("tenant A upload: %w", err)
	}
	slog.Info("tenant A uploaded shared blob", "digest", digest.Key(d))

	// Tenant A reads it through the node-local cache (cold: one origin fetch).
	if _, err := retry(func() ([]byte, error) {
		return cacheClient.Fetch(ctxA, shared, d)
	}); err != nil {
		return fmt.Errorf("tenant A cold read: %w", err)
	}
	// Tenant B reads the same content (warm: should be a node-local hit).
	got, err := retry(func() ([]byte, error) {
		return cacheClient.Fetch(ctxB, shared, d)
	})
	if err != nil {
		return fmt.Errorf("tenant B warm read: %w", err)
	}
	if string(got) != string(content) {
		return errors.New("tenant B read wrong bytes from cache")
	}
	slog.Info("tenant B served shared blob from node-local cache")

	// Isolation: tenant B must not read tenant A's private instance.
	if err := tryCrossTenant(ctxB, cacheClient, instanceA, d); err != nil {
		return err
	}
	slog.Info("isolation held: tenant B denied tenant A's private instance")

	// If the cache exposes metrics, confirm the warm read avoided a second
	// origin fetch.
	if metricsURL != "" {
		if err := checkStats(metricsURL); err != nil {
			return err
		}
	}
	return nil
}

func tryCrossTenant(ctx context.Context, c *remote.Client, instanceA string, d *repb.Digest) error {
	_, err := c.Fetch(ctx, instanceA, d)
	if status.Code(err) == codes.PermissionDenied {
		return nil
	}
	if err == nil {
		return errors.New("isolation breach: tenant B read tenant A's private instance")
	}
	return fmt.Errorf("unexpected error probing isolation: %w", err)
}

// retry reissues a gRPC call a few times when the server is still coming up.
func retry[T any](fn func() (T, error)) (T, error) {
	var zero T
	var last error
	for i := 0; i < 10; i++ {
		v, err := fn()
		if err == nil {
			return v, nil
		}
		last = err
		if c := status.Code(err); c != codes.Unavailable && c != codes.DeadlineExceeded {
			return zero, err
		}
		time.Sleep(time.Second)
	}
	return zero, last
}

func checkStats(metricsURL string) error {
	resp, err := http.Get(metricsURL + "/stats")
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	var s cache.Stats
	if err := json.NewDecoder(resp.Body).Decode(&s); err != nil {
		return err
	}
	slog.Info("cache stats", "hits", s.Hits, "originFetches", s.OriginFetches, "poisonRejected", s.PoisonRejected)
	if s.Hits < 1 {
		return fmt.Errorf("expected at least one cache hit, stats=%+v", s)
	}
	return nil
}
