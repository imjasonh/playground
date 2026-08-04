package gateway

import (
	"context"
	"fmt"
	"io"
	"strings"
	"time"
)

// DialWithLoading writes a wake/loading line ("Starting fortune…") while dial
// runs, then returns the resolved address. Matches the design cold-start UX:
// hold the SSH session and show status until the microVM is ready.
func DialWithLoading(ctx context.Context, out io.Writer, app string, dial DialFunc, req DialRequest) (string, error) {
	if ctx == nil {
		ctx = context.Background()
	}
	type result struct {
		addr string
		err  error
	}
	done := make(chan result, 1)
	go func() {
		addr, err := dial(ctx, req)
		done <- result{addr, err}
	}()

	_, _ = fmt.Fprintf(out, "Starting %s", app)
	ticker := time.NewTicker(400 * time.Millisecond)
	defer ticker.Stop()
	n := 0
	for {
		select {
		case <-ctx.Done():
			_, _ = fmt.Fprintf(out, "\r\n")
			return "", ctx.Err()
		case r := <-done:
			_, _ = fmt.Fprintf(out, "\r\n")
			if r.err != nil {
				return "", r.err
			}
			return r.addr, nil
		case <-ticker.C:
			n = (n + 1) % 4
			dots := strings.Repeat(".", n)
			pad := strings.Repeat(" ", 3-n)
			_, _ = fmt.Fprintf(out, "\rStarting %s%s%s", app, dots, pad)
		}
	}
}
