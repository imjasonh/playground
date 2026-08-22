// Command hello is a minimal Wish SSH app that greets the caller and exits.
package main

import (
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"os/signal"
	"syscall"
	"time"

	"charm.land/log/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
	"charm.land/wish/v2/logging"
)

const defaultAddr = ":2222"

func main() {
	addr := envOr("SSHAPP_ADDR", defaultAddr)
	srv, err := newServer(addr, os.Getenv("SSHAPP_HOST_KEY"), envOr("SSHAPP_HOST_KEY_PATH", ".ssh/host_ed25519"))
	if err != nil {
		log.Fatal("create server", "error", err)
	}

	done := make(chan os.Signal, 1)
	signal.Notify(done, os.Interrupt, syscall.SIGINT, syscall.SIGTERM)

	go func() {
		log.Info("starting SSH server", "addr", addr)
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
			log.Error("listen", "error", err)
			done <- syscall.SIGTERM
		}
	}()

	<-done
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if err := srv.Shutdown(ctx); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
		log.Error("shutdown", "error", err)
		os.Exit(1)
	}
}

func newServer(addr, hostKeyPEM, hostKeyPath string) (*ssh.Server, error) {
	opts := []ssh.Option{
		wish.WithAddress(addr),
		// Accept any public key so a first `ssh hello.example.com` works
		// without provisioning accounts. Password auth stays disabled.
		wish.WithPublicKeyAuth(func(_ ssh.Context, _ ssh.PublicKey) bool {
			return true
		}),
		wish.WithMiddleware(
			helloMiddleware("hello"),
			logging.Middleware(),
		),
	}
	if hostKeyPEM != "" {
		opts = append(opts, wish.WithHostKeyPEM([]byte(hostKeyPEM)))
	} else {
		opts = append(opts, wish.WithHostKeyPath(hostKeyPath))
	}
	return wish.NewServer(opts...)
}

func helloMiddleware(greeting string) wish.Middleware {
	return func(next ssh.Handler) ssh.Handler {
		return func(sess ssh.Session) {
			_, _ = io.WriteString(sess, greet(greeting, sess.User()))
			next(sess)
			_ = sess.Exit(0)
		}
	}
}

func greet(greeting, user string) string {
	if user == "" {
		user = "friend"
	}
	return fmt.Sprintf("%s, %s\n", greeting, user)
}

func envOr(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}
