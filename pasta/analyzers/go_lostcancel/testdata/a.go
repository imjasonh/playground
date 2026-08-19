package a

import (
	"context"
	"time"
)

func badShort(parent context.Context) {
	ctx, _ := context.WithCancel(parent) // want "the cancel function returned by context.WithCancel should be called, not discarded"
	_ = ctx
}

func badAssign(parent context.Context) {
	var ctx context.Context
	ctx, _ = context.WithTimeout(parent, time.Second) // want "the cancel function returned by context.WithTimeout should be called, not discarded"
	_ = ctx
}

func ok(parent context.Context) {
	ctx, cancel := context.WithCancel(parent)
	defer cancel()
	_ = ctx
}
