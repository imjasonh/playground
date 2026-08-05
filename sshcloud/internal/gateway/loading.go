package gateway

import (
	"context"
	"errors"
	"fmt"
	"io"
	"strings"
	"time"
)

// DialWithLoading writes a wake/loading line ("Starting fortune…") while dial
// runs, then returns the resolved address. Matches the design cold-start UX:
// hold the SSH session and show status until the microVM is ready.
func DialWithLoading(ctx context.Context, out io.Writer, app string, dial DialFunc, req DialRequest) (DialTarget, error) {
	if ctx == nil {
		ctx = context.Background()
	}
	type result struct {
		target DialTarget
		err    error
	}
	done := make(chan result, 1)
	retries := make(chan error, 1)
	go func() {
		retryFor := req.RetryFor
		if retryFor <= 0 {
			retryFor = time.Minute
		}
		deadline := time.Now().Add(retryFor)
		delay := 250 * time.Millisecond
		for {
			target, err := dial(ctx, req)
			if err == nil || !temporary(err) || time.Now().Add(delay).After(deadline) {
				done <- result{target, err}
				return
			}
			select {
			case retries <- err:
			default:
			}
			timer := time.NewTimer(delay)
			select {
			case <-ctx.Done():
				timer.Stop()
				done <- result{err: ctx.Err()}
				return
			case <-timer.C:
			}
			if delay < 5*time.Second {
				delay *= 2
				if delay > 5*time.Second {
					delay = 5 * time.Second
				}
			}
		}
	}()

	_, _ = fmt.Fprintf(out, "Starting %s", app)
	ticker := time.NewTicker(400 * time.Millisecond)
	defer ticker.Stop()
	n := 0
	for {
		select {
		case <-ctx.Done():
			_, _ = fmt.Fprintf(out, "\r\n")
			return DialTarget{}, ctx.Err()
		case r := <-done:
			_, _ = fmt.Fprintf(out, "\r\n")
			if r.err != nil {
				return DialTarget{}, r.err
			}
			return r.target, nil
		case err := <-retries:
			message := err.Error()
			if len(message) > 120 {
				message = message[:120] + "…"
			}
			_, _ = fmt.Fprintf(out, "\rStarting %s — retrying: %s\r\n", app, message)
		case <-ticker.C:
			n = (n + 1) % 4
			dots := strings.Repeat(".", n)
			pad := strings.Repeat(" ", 3-n)
			_, _ = fmt.Fprintf(out, "\rStarting %s%s%s", app, dots, pad)
		}
	}
}

func temporary(err error) bool {
	type temporaryError interface {
		Temporary() bool
	}
	var candidate temporaryError
	return errors.As(err, &candidate) && candidate.Temporary()
}
