package gateway

import (
	"context"
	"io"
	"sort"
	"strconv"
)

// RunMenu shows the hub app picker and hands off to an app or deploy.
func RunMenu(ctx context.Context, ch io.ReadWriter, hub *Hub, keyFP, userID string) int {
	return RunMenuSession(ctx, ClientSession{IO: ch, Stderr: ch, Spec: &SessionSpec{StartType: SessionShell, PTY: true}}, hub, keyFP, userID)
}

func RunMenuSession(ctx context.Context, client ClientSession, hub *Hub, keyFP, userID string) int {
	return runMenu(ctx, newSessionTerm(client), hub, keyFP, userID)
}

func runMenu(ctx context.Context, t *term, hub *Hub, keyFP, userID string) int {
	if userID == "" {
		t.Printf("Not logged in. Complete join first.\n")
		return 0
	}

	for {
		if err := hub.authorizeUse(keyFP); err != nil {
			t.Printf("%s\n", forbiddenMessage(err))
			return 1
		}
		apps, err := hub.Store.ListApps(ctx, userID)
		if err != nil {
			t.Printf("error listing apps: %v\n", err)
			return 0
		}

		type item struct {
			label string
			kind  string // "app" | "deploy"
			app   string
		}
		var items []item
		sort.Slice(apps, func(i, j int) bool { return apps[i].Name < apps[j].Name })
		for _, a := range apps {
			label := a.Name
			if a.DrainingGen != "" || a.DrainUntilUnix > 0 {
				label += " — draining"
			}
			items = append(items, item{label: label, kind: "app", app: a.Name})
		}
		items = append(items, item{label: "deploy", kind: "deploy"})

		t.Printf("Apps for %s\n", userID)
		t.Printf("────────────\n")
		if len(apps) == 0 {
			t.Printf("(no apps yet — deploy one)\n")
		}
		for i, it := range items {
			t.Printf("  %d) %s\n", i+1, it.label)
		}
		t.Printf("  q) quit\n")
		t.Printf("Select: ")

		line, err := t.ReadLine()
		if err != nil {
			return 0
		}
		if line == "q" || line == "quit" {
			t.Printf("Bye.\n")
			return 0
		}
		n, err := strconv.Atoi(line)
		if err != nil || n < 1 || n > len(items) {
			t.Printf("Invalid selection\n\n")
			continue
		}
		it := items[n-1]
		switch it.kind {
		case "deploy":
			if err := hub.authorizeDeploy(keyFP, userID); err != nil {
				t.Printf("%s\n", forbiddenMessage(err))
				return 1
			}
			_ = runDeploy(ctx, t, hub, keyFP, userID, "")
			t.Printf("\n")
		case "app":
			res, err := hub.OpenApp(ctx, keyFP, userID, it.app)
			if err != nil {
				if isForbidden(err) {
					t.Printf("%s\n", forbiddenMessage(err))
					return 1
				}
				t.Printf("%v\n\n", err)
				continue
			}
			if res.Action == ActionRejectBusy {
				t.Printf("%s\n\n", res.Message)
				continue
			}
			sessCtx, cancel := hub.BindSession(ctx, res.Session)
			runAppStub(sessCtx, t, hub, res)
			cancel()
			hub.ReleaseSession(res.Session)
			t.Printf("\n")
		}
	}
}
