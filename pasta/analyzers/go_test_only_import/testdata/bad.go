package bad

import (
	"context"

	tt "github.com/imjasonh/playground/testtrace" // want "testtrace instruments tests"
)

func f(ctx context.Context) {
	tt.Install(nil)
}
