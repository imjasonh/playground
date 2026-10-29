package a

import "context"

type bad struct {
	ctx context.Context // want "stored on a struct"
	n   int
}

type alsoBad struct {
	ctx *context.Context // want "stored on a struct"
}

type ok struct {
	n int
}

func f(ctx context.Context) {}
