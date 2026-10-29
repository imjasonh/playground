package a

import "context"

type S struct{}

func good(ctx context.Context, n int) {}

func bad(n int, ctx context.Context) {} // want "context.Context parameter is not first"

func (s *S) goodMethod(ctx context.Context, n int) {}

func (s *S) badMethod(n int, ctx context.Context) {} // want "context.Context parameter is not first"

func results() (ctx context.Context, err error) {
	return context.Background(), nil
}

func twoContexts(ctx context.Context, parent context.Context) {}

func nestedOK(h func(context.Context, int)) {}

func registerOK(mutating bool, h func(context.Context, int)) {}

func callbackBad(h func(n int, ctx context.Context)) {} // want "context.Context parameter is not first"

type I interface {
	M(n int, ctx context.Context) // want "context.Context parameter is not first"
}
