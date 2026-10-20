// Command hello is a minimal Wish SSH app that greets the caller and exits.
package main

import (
	"context"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/signal"
	"syscall"
	"time"

	"charm.land/ssh"
	"charm.land/wish/v2"
	"charm.land/wish/v2/logging"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"
)

var env = envconfig.MustProcess(context.Background(), &struct {
	Addr        string `env:"SSHAPP_ADDR, default=:2222"`
	HostKey     string `env:"SSHAPP_HOST_KEY"`
	HostKeyPath string `env:"SSHAPP_HOST_KEY_PATH, default=.ssh/host_ed25519"`
}{})

func main() {
	srv, err := newServer(env.Addr, env.HostKey, env.HostKeyPath)
	if err != nil {
		slog.Error("create server", "error", err)
		os.Exit(1)
	}

	done := make(chan os.Signal, 1)
	signal.Notify(done, os.Interrupt, syscall.SIGINT, syscall.SIGTERM)

	go func() {
		slog.Info("starting SSH server", "addr", env.Addr)
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
			slog.Error("listen", "error", err)
			done <- syscall.SIGTERM
		}
	}()

	<-done
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if err := srv.Shutdown(ctx); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
		slog.Error("shutdown", "error", err)
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
