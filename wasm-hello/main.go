//go:build !wasip1

// Command wasm-hello serves the hello-world service on a real TCP port.
//
// This is the same http.Handler the wasm build exports, running the ordinary
// way. It exists so the service can be developed and debugged without a wasm
// runtime in the loop, and so `go build ./...` and `go test ./...` mean
// something on a machine that is not wasip1.
package main

import (
	"context"
	"errors"
	"flag"
	"log"
	"net/http"
	"os/signal"
	"syscall"
	"time"

	"github.com/imjasonh/playground/wasm-hello/handler"
)

func main() {
	addr := flag.String("addr", "127.0.0.1:8080", "address to listen on")
	greeting := flag.String("greeting", "", "what the root page says")
	flag.Parse()

	server := &http.Server{
		Addr:              *addr,
		Handler:           handler.New(*greeting),
		ReadHeaderTimeout: 5 * time.Second,
	}

	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGINT, syscall.SIGTERM)
	defer stop()

	go func() {
		<-ctx.Done()
		shutdown, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		_ = server.Shutdown(shutdown)
	}()

	log.Printf("listening on http://%s", *addr)
	if err := server.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
		log.Fatal(err)
	}
}
