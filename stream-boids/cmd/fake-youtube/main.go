// Command fake-youtube serves a fake YouTube Data API for running
// stream-boids locally. Open its address in a browser to set the viewer
// count and send chat messages, Super Chats, and memberships.
package main

import (
	"context"
	"errors"
	"log/slog"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/sethvargo/go-envconfig"

	"github.com/imjasonh/playground/stream-boids/internal/fakeyt"
)

var env = envconfig.MustProcess(context.Background(), &struct {
	Addr string `env:"ADDR, default=127.0.0.1:8090"`
	// Key, when set, is the API key requests must send.
	Key          string        `env:"FAKE_YOUTUBE_KEY"`
	PollInterval time.Duration `env:"POLL_INTERVAL, default=2s"`
}{})

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	fs := fakeyt.New()
	fs.Key = env.Key
	fs.PollInterval = env.PollInterval
	srv := &http.Server{Addr: env.Addr, Handler: fs, ReadHeaderTimeout: 10 * time.Second}
	go func() {
		<-ctx.Done()
		shutdown, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		srv.Shutdown(shutdown)
	}()
	slog.Info("serving fake YouTube", "url", "http://"+env.Addr+"/", "api", "http://"+env.Addr+"/youtube/v3",
		"video", fakeyt.VideoID, "channel", fakeyt.ChannelID)
	if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
		clog.Fatal("serving", "error", err)
	}
}
