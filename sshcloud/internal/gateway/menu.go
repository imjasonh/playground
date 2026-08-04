package gateway

import (
	"context"
	"io"
	"sort"
	"strconv"

	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// RunMenu shows the hub app picker and hands off to an app or deploy stub.
func RunMenu(ctx context.Context, ch io.ReadWriter, hub *Hub, keyFP, userID string) {
	_ = keyFP
	t := newTerm(ch)
	if userID == "" {
		t.Printf("Not logged in. Complete join first.\n")
		return
	}

	for {
		apps, err := hub.Store.ListApps(ctx, userID)
		if err != nil {
			t.Printf("error listing apps: %v\n", err)
			return
		}

		type item struct {
			label string
			kind  string // "app" | "demo" | "deploy"
			app   string
		}
		var items []item
		seen := map[string]bool{}
		for _, a := range apps {
			items = append(items, item{label: a.Name, kind: "app", app: a.Name})
			seen[a.Name] = true
		}
		var demos []string
		for demo := range store.PlatformDemos {
			if !seen[demo] {
				demos = append(demos, demo)
			}
		}
		sort.Strings(demos)
		for _, demo := range demos {
			items = append(items, item{label: demo + " (demo)", kind: "demo", app: demo})
		}
		items = append(items, item{label: "deploy", kind: "deploy"})

		t.Printf("Apps for %s\n", userID)
		t.Printf("────────────\n")
		for i, it := range items {
			t.Printf("  %d) %s\n", i+1, it.label)
		}
		t.Printf("  q) quit\n")
		t.Printf("Select: ")

		line, err := t.ReadLine()
		if err != nil {
			return
		}
		if line == "q" || line == "quit" {
			t.Printf("Bye.\n")
			return
		}
		n, err := strconv.Atoi(line)
		if err != nil || n < 1 || n > len(items) {
			t.Printf("Invalid selection\n\n")
			continue
		}
		it := items[n-1]
		switch it.kind {
		case "deploy":
			t.Printf("deploy: not implemented yet\n\n")
		case "app", "demo":
			res, err := hub.OpenApp(ctx, userID, it.app)
			if err != nil {
				t.Printf("%v\n\n", err)
				continue
			}
			if res.Action == ActionRejectBusy {
				t.Printf("%s\n\n", res.Message)
				continue
			}
			RunAppStub(ctx, ch, hub, res)
			hub.ReleaseSession(res.Session)
			t.Printf("\n")
		}
	}
}
