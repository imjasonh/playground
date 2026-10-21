package p

import (
	"log/slog"

	"github.com/chainguard-dev/clog"
)

type config struct {
	level string
	out   *bytesBuffer
}

type bytesBuffer struct{}

func take(log *slog.Logger, clogger *clog.Logger) *slog.Logger {
	return log
}

func local() {
	log := slog.Default()
	_ = log
	_ = take(log, nil)
}

type client interface {
	SetLogger(logger *slog.Logger)
}

func discard() *slog.Logger { return slog.New(slog.DiscardHandler) }
