package a

import (
	"context"
	"testing"
)

func TestBad(t *testing.T) {
	_ = context.Background() // want "use t.Context() instead of context.Background()"
	_ = context.TODO()       // want "use t.Context() instead of context.TODO()"
	ctx, cancel := context.WithCancel(context.Background()) // want "use t.Context() instead of context.Background()"
	defer cancel()
	_ = ctx
}
