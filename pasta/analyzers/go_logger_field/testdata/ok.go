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

func local() {
	log := slog.Default()
	_ = log
	clogger := clog.New(slog.DiscardHandler)
	_ = clogger
}

func discard() *slog.Logger { return slog.New(slog.DiscardHandler) }

func makeLogger() *clog.Logger { return clog.New(slog.DiscardHandler) }

func parenthesized() (*slog.Logger, error) {
	return slog.New(slog.DiscardHandler), nil
}

func namedResult() (log *slog.Logger) { return nil }
