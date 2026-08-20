package a

import "context"

// Non-test file: context.Background must not be flagged.
func run() {
	_ = context.Background()
	_ = context.TODO()
}
