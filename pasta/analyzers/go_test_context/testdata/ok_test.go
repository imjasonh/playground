package a

import (
	"context"
	"testing"
)

func TestOK(t *testing.T) {
	_ = t.Context()
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	_ = ctx
}
