package gateway

import (
	"context"
	"io"
	"strings"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// Common local account names that collide with bare `ssh host` routing.
var commonLocalUsernames = map[string]struct{}{
	"ubuntu": {}, "debian": {}, "admin": {}, "user": {}, "pi": {},
	"ec2-user": {}, "fedora": {}, "centos": {}, "arch": {},
	"alice": {}, "bob": {}, "dev": {}, "me": {},
}

// RunDeploy is the deploy TUI (`ssh deploy@…` or menu → deploy).
// It registers a digest-pinned app and runs drain/kick cutover when a Controller is set.
func RunDeploy(ctx context.Context, ch io.ReadWriter, hub *Hub, userID string) {
	runDeploy(ctx, newTerm(ch), hub, userID)
}

func runDeploy(ctx context.Context, t *term, hub *Hub, userID string) {
	if userID == "" {
		t.Printf("Not logged in. Complete join first.\n")
		return
	}

	t.Printf("Deploy\n")
	t.Printf("──────\n")
	t.Printf("Create or update an app from a digest-pinned OCI image.\n")
	t.Printf("PID 1 must speak SSH on :22 and trust the platform user CA.\n\n")

	appName, ok := promptAppName(ctx, t, hub, userID)
	if !ok {
		return
	}
	img, ok := promptImage(t)
	if !ok {
		return
	}
	tier, ok := promptTier(t)
	if !ok {
		return
	}
	strategy, ok := promptStrategy(t)
	if !ok {
		return
	}

	existing, err := hub.Store.GetApp(ctx, userID, appName)
	if err != nil {
		t.Printf("error: %v\n", err)
		return
	}
	updated := existing != nil

	if hub.Cutover != nil {
		if existing == nil {
			if err := hub.Store.UpsertApp(ctx, store.App{
				Owner:           userID,
				Name:            appName,
				Tier:            tier,
				SessionStrategy: strategy,
			}); err != nil {
				t.Printf("deploy failed: %v\n", err)
				return
			}
		} else {
			existing.Tier = tier
			existing.SessionStrategy = strategy
			if err := hub.Store.UpsertApp(ctx, *existing); err != nil {
				t.Printf("deploy failed: %v\n", err)
				return
			}
		}
		res, err := hub.Cutover.Deploy(ctx, cutover.Request{
			User:     userID,
			App:      appName,
			Image:    img,
			Strategy: strategy,
		})
		if err != nil {
			t.Printf("cutover failed: %v\n", err)
			return
		}
		verb := "Created"
		if updated {
			verb = "Updated"
		}
		t.Printf("\n✓ %s %s (%s)\n", verb, appName, tier)
		t.Printf("  image:    %s\n", img)
		t.Printf("  strategy: %s\n", strategyLabel(strategy))
		t.Printf("  generation: %s\n", res.ActiveGen)
		if res.DrainingGen != "" {
			until := res.DrainUntil.UTC().Format("15:04:05 UTC")
			t.Printf("  draining:   %s until %s\n", displayGen(res.DrainingGen), until)
		}
		t.Printf("\nConnect with:\n")
		t.Printf("  ssh %s@<host>\n", appName)
		t.Printf("\nPress enter to return.\n")
		_, _ = t.ReadLine()
		return
	}

	app := store.App{
		Owner:           userID,
		Name:            appName,
		Image:           img,
		Tier:            tier,
		SessionStrategy: strategy,
	}
	if err := hub.Store.UpsertApp(ctx, app); err != nil {
		t.Printf("deploy failed: %v\n", err)
		return
	}

	verb := "Created"
	if updated {
		verb = "Updated"
	}
	t.Printf("\n✓ %s %s (%s)\n", verb, appName, tier)
	t.Printf("  image:    %s\n", img)
	t.Printf("  strategy: %s\n", strategyLabel(strategy))
	t.Printf("\n")
	t.Printf("Note: instance cutover is not attached in this gateway process.\n")
	t.Printf("The app is registered. Connect with:\n")
	t.Printf("  ssh %s@<host>\n", appName)
	t.Printf("\nPress enter to return.\n")
	_, _ = t.ReadLine()
}

func displayGen(gen string) string {
	if gen == "" {
		return "(legacy)"
	}
	return gen
}

func promptAppName(ctx context.Context, t *term, hub *Hub, userID string) (string, bool) {
	for {
		t.Printf("App name: ")
		name, err := t.ReadLine()
		if err != nil {
			return "", false
		}
		if err := names.ValidateIdent(name); err != nil {
			t.Printf("Invalid: %v\n", err)
			continue
		}
		if _, common := commonLocalUsernames[name]; common {
			t.Printf("Warning: %q matches a common local username — bare\n", name)
			t.Printf("  `ssh <host>` will deep-link into this app (use menu@).\n")
		}
		existing, err := hub.Store.GetApp(ctx, userID, name)
		if err != nil {
			t.Printf("error: %v\n", err)
			return "", false
		}
		if existing != nil {
			t.Printf("App %q exists (image: %s).\n", name, displayImage(existing))
			t.Printf("Update it? [Y/n]: ")
			ans, err := t.ReadLine()
			if err != nil {
				return "", false
			}
			ans = strings.ToLower(ans)
			if ans == "n" || ans == "no" {
				continue
			}
		}
		return name, true
	}
}

func promptImage(t *term) (string, bool) {
	for {
		t.Printf("Image (repo@sha256:…): ")
		ref, err := t.ReadLine()
		if err != nil {
			return "", false
		}
		if err := image.ValidateDigestPinned(ref); err != nil {
			t.Printf("Invalid: %v\n", err)
			continue
		}
		return strings.TrimSpace(ref), true
	}
}

func promptTier(t *term) (string, bool) {
	for {
		t.Printf("Tier [tiny/small] (default tiny): ")
		line, err := t.ReadLine()
		if err != nil {
			return "", false
		}
		line = strings.ToLower(strings.TrimSpace(line))
		if line == "" {
			return "tiny", true
		}
		if line == "tiny" || line == "small" {
			return line, true
		}
		t.Printf("Invalid: choose tiny or small\n")
	}
}

func promptStrategy(t *term) (string, bool) {
	t.Printf("\nOn deploy, active sessions:\n")
	t.Printf("  1) route new to new, drain old; kick after timeout (default)\n")
	t.Printf("  2) kick now\n")
	for {
		t.Printf("Select [1]: ")
		line, err := t.ReadLine()
		if err != nil {
			return "", false
		}
		line = strings.ToLower(strings.TrimSpace(line))
		switch line {
		case "", "1", "drain":
			return store.StrategyDrain, true
		case "2", "kick":
			return store.StrategyKick, true
		default:
			t.Printf("Invalid: choose 1 or 2\n")
		}
	}
}

func strategyLabel(s string) string {
	switch s {
	case store.StrategyKick:
		return "kick now"
	default:
		return "drain + kick-on-timeout"
	}
}

func displayImage(a *store.App) string {
	if a.Image == "" {
		return "(none)"
	}
	return a.Image
}
