package p

import (
	"log/slog"

	"github.com/chainguard-dev/clog"
)

type sim struct {
	log *clog.Logger // want "logger stored on a struct"
}

type store struct {
	log *slog.Logger // want "logger stored on a struct"
}

type byValue struct {
	log  slog.Logger // want "logger stored on a struct"
	clog clog.Logger // want "logger stored on a struct"
}

type embedded struct {
	*slog.Logger // want "logger stored on a struct"
}

type pair struct {
	a, b *slog.Logger // want "logger stored on a struct"
}

func anon() {
	_ = struct {
		log *clog.Logger // want "logger stored on a struct"
	}{}
}

func take(
	log *slog.Logger, // want "logger passed to a function"
	clogger *clog.Logger, // want "logger passed to a function"
) {
	_ = log
	_ = clogger
}

func takeValue(
	log slog.Logger, // want "logger passed to a function"
	clogger clog.Logger, // want "logger passed to a function"
) {
	_ = log
	_ = clogger
}

type client interface {
	SetLogger(logger *slog.Logger) // want "logger passed to a function"
}

type sink func(log *slog.Logger) // want "logger passed to a function"

func literal(f func(log *clog.Logger)) { // want "logger passed to a function"
	f(nil)
}
