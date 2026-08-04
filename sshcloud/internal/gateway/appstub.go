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

// RunAppStub connects to the app backend (cert hop) or falls back to a stub UI.
func RunAppStub(ctx context.Context, ch io.ReadWriter, hub *Hub, res Result) {
	runAppStub(ctx, newTerm(ch), hub, res)
}

func runAppStub(ctx context.Context, t *term, hub *Hub, res Result) {
	if hub.UserCA != nil && hub.Dial != nil {
		img := ""
		if a, err := hub.Store.GetApp(ctx, res.User, res.App); err == nil && a != nil {
			img = a.Image
		}
		addr, err := DialWithLoading(ctx, t.out, res.App, hub.Dial, DialRequest{
			User:  res.User,
			App:   res.App,
			Gen:   res.Gen,
			Image: img,
		})
		if err != nil {
			t.Printf("backend error: %v\n", err)
			return
		}
		if err := ProxySSH(ctx, t.rw, hub.UserCA, res.User, addr); err != nil {
			if ctx.Err() != nil {
				return
			}
			t.Printf("proxy error: %v\n", err)
		}
		return
	}

	// Fallback when CA/backend not configured (unit tests / misconfig).
	t.Printf("app %q: no backend configured\n", res.App)
	t.Printf("(deploy a digest-pinned image and run gateway with -agent-url)\n")
	if res.App == "fortune" {
		t.Printf("\n── sample fortune ──\n")
		t.Printf("%s\n", fortunes[rand.Intn(len(fortunes))])
		t.Printf("───────────────────\n")
	}
	t.Printf("Press enter to return.\n")
	_, _ = t.ReadLine()
}
