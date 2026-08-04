package gateway

import (
	"context"
	"io"
	"math/rand"

	"golang.org/x/crypto/ssh"
)

var fortunes = []string{
	"The only way to do great work is to love what you do.",
	"ssh more, click less.",
	"MicroVMs are just very small computers with trust issues.",
	"Your future holds a short-lived SSH certificate.",
	"Fortune favors the joined.",
}

// RunAppStub connects to the app backend (cert hop) or falls back to a stub UI.
func RunAppStub(ctx context.Context, ch io.ReadWriter, hub *Hub, res Result) int {
	return runAppStub(ctx, newTerm(ch), hub, res)
}

func runAppStub(ctx context.Context, t *term, hub *Hub, res Result) int {
	if hub.UserCA != nil && hub.Dial != nil {
		img, tier := res.Image, res.Tier
		if img == "" || tier == "" {
			if a, err := hub.Store.GetApp(ctx, res.User, res.App); err == nil && a != nil {
				if img == "" {
					img = a.Image
				}
				if tier == "" {
					tier = a.Tier
				}
			}
		}
		if tier == "" {
			tier = "tiny"
		}
		addr, err := DialWithLoading(ctx, t.out, res.App, hub.Dial, DialRequest{
			User:   res.User,
			App:    res.App,
			Gen:    res.Gen,
			Image:  img,
			Tier:   tier,
			NoIdle: true,
		})
		if err != nil {
			t.Printf("backend error: %v\n", err)
			return 1
		}
		if err := ProxySSH(ctx, t.rw, hub.UserCA, res.User, addr); err != nil {
			if ctx.Err() != nil {
				return 1
			}
			t.Printf("proxy error: %v\n", err)
			if exitErr, ok := err.(*ssh.ExitError); ok {
				return exitErr.ExitStatus()
			}
			return 1
		}
		return 0
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
	return 0
}
