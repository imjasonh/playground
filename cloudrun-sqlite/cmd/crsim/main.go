// Command crsim runs a container command the way Cloud Run would: one
// instance started on the first request, scaled to zero when idle, stopped
// with SIGTERM and then SIGKILL, optionally frozen between requests.
//
//	crsim -listen :8080 -idle-timeout 30s -throttle -- ./cloudrun-sqlite
//
// Control it with POST /_crsim/deploy?overlap=5s, /_crsim/crash, and
// /_crsim/scale-to-zero, and read GET /_crsim/stats.
package main

import (
	"flag"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/crsim"
)

type envFlag []string

func (e *envFlag) String() string     { return strings.Join(*e, ",") }
func (e *envFlag) Set(v string) error { *e = append(*e, v); return nil }

func main() {
	var cfg crsim.Config
	var env envFlag
	listen := flag.String("listen", ":8080", "address to serve the simulated service on")
	flag.DurationVar(&cfg.IdleTimeout, "idle-timeout", 0, "scale to zero after this long without requests (0 disables)")
	flag.DurationVar(&cfg.GracePeriod, "grace", 0, "time between SIGTERM and SIGKILL (default 10s)")
	flag.BoolVar(&cfg.Throttle, "throttle", false, "freeze instances between requests (request-based billing)")
	flag.Var(&env, "env", "KEY=VALUE added to each instance's environment (repeatable)")
	flag.Parse()
	if flag.NArg() == 0 {
		fmt.Fprintln(os.Stderr, "usage: crsim [flags] -- command [args...]")
		os.Exit(2)
	}
	cfg.Command = flag.Args()
	cfg.Env = env
	cfg.Logger = slog.New(slog.NewTextHandler(os.Stderr, nil)).With("component", "crsim")
	slog.SetDefault(cfg.Logger)

	sim := crsim.New(cfg)
	go func() {
		sig := make(chan os.Signal, 1)
		signal.Notify(sig, os.Interrupt, syscall.SIGTERM)
		<-sig
		sim.Close()
		os.Exit(0)
	}()
	cfg.Logger.Info("serving", "listen", *listen, "command", cfg.Command)
	if err := http.ListenAndServe(*listen, sim); err != nil {
		clog.Fatal("listen", "error", err)
	}
}
