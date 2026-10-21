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
