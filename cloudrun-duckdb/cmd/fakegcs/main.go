// Command fakegcs serves the part of the Cloud Storage JSON API that
// cloudrun-duckdb uses, from a local directory. With -latency it adds the
// same per-request latency and bandwidth caps as cloudrun-sqlite's latproxy.
//
//	fakegcs -listen 127.0.0.1:9100 -root /tmp/fakegcs -latency
//	cloudrun-duckdb -replica-url 'gs://bucket/db?endpoint=http://127.0.0.1:9100'
package main

import (
	"flag"
	"log/slog"
	"net/http"
	"os"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/fakegcs"
)

func main() {
	listen := flag.String("listen", "127.0.0.1:9100", "listen address")
	root := flag.String("root", "", "directory that holds one subdirectory per bucket")
	latency := flag.Bool("latency", false, "add latproxy's latency and bandwidth model")
	m := fakegcs.LatProxy
	flag.DurationVar(&m.Get, "get", m.Get, "GET latency, with -latency")
	flag.DurationVar(&m.List, "list", m.List, "LIST latency, with -latency")
	flag.DurationVar(&m.Put, "put", m.Put, "upload latency, with -latency")
	flag.Int64Var(&m.Download, "bw", m.Download, "download and upload bandwidth per request in bytes per second, with -latency (0 is unlimited)")
	flag.Parse()
	if *root == "" {
		clog.Fatal("set -root")
	}
	if err := os.MkdirAll(*root, 0o755); err != nil {
		clog.Fatal("create root", "error", err)
	}
	var l fakegcs.Latency
	if *latency {
		m.Upload = m.Download
		l = m
	}
	srv := fakegcs.New(*root, l)
	go func() {
		for range time.Tick(10 * time.Second) {
			c := srv.Counts()
			slog.Info("requests", "get", c.Get, "list", c.List, "create", c.Create, "delete", c.Delete)
		}
	}()
	slog.Info("listening", "addr", *listen, "root", *root, "latency", *latency)
	clog.Fatal("serve", "error", http.ListenAndServe(*listen, srv))
}
