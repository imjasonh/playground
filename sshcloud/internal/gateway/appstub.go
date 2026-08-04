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

// RunAppStub is an in-process stand-in until Firecracker proxying exists.
func RunAppStub(ctx context.Context, ch io.ReadWriter, hub *Hub, res Result) {
	_ = ctx
	_ = hub
	t := newTerm(ch)
	switch res.App {
	case "fortune":
		t.Printf("── fortune ──\n")
		t.Printf("%s\n", fortunes[rand.Intn(len(fortunes))])
		t.Printf("─────────────\n")
		t.Printf("(in-process stub — Firecracker proxy coming next)\n")
		t.Printf("Press enter to return.\n")
		_, _ = t.ReadLine()
	default:
		t.Printf("app %q: no stub handler (Firecracker proxy not wired)\n", res.App)
		t.Printf("Press enter to return.\n")
		_, _ = t.ReadLine()
	}
}
