package gateway

import (
	"context"
	"io"
	"math/rand"
)

var fortunes = []string{
	"The only way to do great work is to love what you do.",
	"ssh more, click less.",
	"MicroVMs are just very small computers with trust issues.",
	"Your future holds a short-lived SSH certificate.",
	"Fortune favors the joined.",
}

// RunAppStub connects to the app backend (cert hop) or falls back to in-process fortune.
func RunAppStub(ctx context.Context, ch io.ReadWriter, hub *Hub, res Result) {
	_ = ctx
	if hub.UserCA != nil && hub.Dial != nil {
		addr, err := hub.Dial(res.User, res.App)
		if err != nil {
			t := newTerm(ch)
			t.Printf("backend error: %v\n", err)
			return
		}
		if err := ProxySSH(ch, hub.UserCA, res.User, addr); err != nil {
			t := newTerm(ch)
			t.Printf("proxy error: %v\n", err)
		}
		return
	}

	// Fallback when CA/backend not configured (unit tests).
	t := newTerm(ch)
	switch res.App {
	case "fortune":
		t.Printf("── fortune ──\n")
		t.Printf("%s\n", fortunes[rand.Intn(len(fortunes))])
		t.Printf("─────────────\n")
		t.Printf("(in-process stub)\n")
		t.Printf("Press enter to return.\n")
		_, _ = t.ReadLine()
	default:
		t.Printf("app %q: no backend\n", res.App)
		t.Printf("Press enter to return.\n")
		_, _ = t.ReadLine()
	}
}
