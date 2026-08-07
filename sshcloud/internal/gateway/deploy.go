package gateway

import (
	"context"
	"fmt"
	"io"
	"strings"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// Common local account names that collide with bare `ssh host` routing.
var commonLocalUsernames = map[string]struct{}{
	"ubuntu": {}, "debian": {}, "admin": {}, "user": {}, "pi": {},
	"ec2-user": {}, "fedora": {}, "centos": {}, "arch": {},
	"alice": {}, "bob": {}, "dev": {}, "me": {},
}

// RunDeploy is the deploy TUI (`ssh deploy@…` or menu → deploy).
// When execCmd is non-empty (SSH exec args), runs non-interactively and
// returns a process exit code (0 ok, 1 failure).
func RunDeploy(ctx context.Context, ch io.ReadWriter, hub *Hub, keyFP, userID, execCmd string) int {
	return RunDeploySession(ctx, ClientSession{IO: ch, Stderr: ch, Spec: &SessionSpec{StartType: SessionShell, PTY: true}}, hub, keyFP, userID, execCmd)
}

func RunDeploySession(ctx context.Context, client ClientSession, hub *Hub, keyFP, userID, execCmd string) int {
	t := newSessionTerm(client)
	return runDeploy(ctx, t, hub, keyFP, userID, execCmd)
}

func runDeploy(ctx context.Context, t *term, hub *Hub, keyFP, userID, execCmd string) int {
	if userID == "" {
		t.Printf("Not logged in. Complete join first.\n")
		return 1
	}
	if err := hub.authorizeDeploy(keyFP, userID); err != nil {
		t.Printf("%s\n", forbiddenMessage(err))
		return 1
	}

	execCmd = strings.TrimSpace(execCmd)
	if execCmd != "" {
		args, err := ParseDeployArgs(splitArgs(execCmd))
		if err != nil {
			t.Printf("deploy: %v\n", err)
			return 1
		}
		updated, err := applyDeploy(ctx, hub, keyFP, userID, args, true)
		if err != nil {
			if isForbidden(err) {
				t.Printf("%s\n", forbiddenMessage(err))
				return 1
			}
			t.Printf("deploy failed: %v\n", err)
			return 1
		}
		printDeployOK(t, args, hub, ctx, userID, updated, false)
		return 0
	}

	t.Printf("Deploy\n")
	t.Printf("──────\n")
	t.Printf("Create or update an app from a digest-pinned OCI image.\n")
	t.Printf("PID 1 must speak SSH on :22 and trust the platform user CA.\n\n")
	t.Printf("Non-interactive: ssh deploy@host fortune --image=repo@sha256:… [--tier=tiny] [--strategy=kick] --yes\n\n")

	appName, ok := promptAppName(ctx, t, hub, userID)
	if !ok {
		return 1
	}
	img, ok := promptImage(t)
	if !ok {
		return 1
	}
	tier, ok := promptTier(t)
	if !ok {
		return 1
	}
	strategy, ok := promptStrategy(t)
	if !ok {
		return 1
	}
	args := DeployArgs{Name: appName, Image: img, Tier: tier, Strategy: strategy, Yes: true}
	updated, err := applyDeploy(ctx, hub, keyFP, userID, args, false)
	if err != nil {
		if isForbidden(err) {
			t.Printf("%s\n", forbiddenMessage(err))
			return 1
		}
		t.Printf("deploy failed: %v\n", err)
		return 1
	}
	printDeployOK(t, args, hub, ctx, userID, updated, true)
	return 0
}

func applyDeploy(ctx context.Context, hub *Hub, keyFP, userID string, args DeployArgs, requireYes bool) (updated bool, err error) {
	if err := hub.authorizeDeploy(keyFP, userID); err != nil {
		return false, err
	}
	if err := image.ValidateAllowedRegistry(args.Image, hub.AllowedRegistries); err != nil {
		return false, err
	}
	unlock := hub.lockUser(userID)
	defer unlock()
	existing, err := hub.Store.GetApp(ctx, userID, args.Name)
	if err != nil {
		return false, err
	}
	updated = existing != nil
	if existing != nil && requireYes && !args.Yes {
		return false, fmt.Errorf("app %q exists; pass --yes to update", args.Name)
	}
	if err := hub.authorizeDeploy(keyFP, userID); err != nil {
		return false, err
	}
	// An identical artifact+tier request is an observation, not a deploy:
	// do not mutate strategy/state, verify/wake a VM, or consume quota.
	if existing != nil && existing.Image == args.Image && existing.Tier == args.Tier {
		return true, nil
	}
	if existing == nil {
		apps, err := hub.Store.ListApps(ctx, userID)
		if err != nil {
			return false, err
		}
		if len(apps) >= hub.limits().AppsPerUser {
			return false, quota.ErrExceeded{Kind: "apps", Limit: hub.limits().AppsPerUser}
		}
	}
	// Recheck after waiting on the per-user deploy lock and immediately before
	// quota/control-plane mutation so a refreshed revocation wins the race.
	if err := hub.authorizeDeploy(keyFP, userID); err != nil {
		return false, err
	}
	if err := hub.allowDeploy(ctx, userID, quota.NewEventID("deploy")); err != nil {
		return false, err
	}

	if hub.Cutover != nil {
		_, err := hub.Cutover.Deploy(ctx, cutover.Request{
			User:     userID,
			App:      args.Name,
			Image:    args.Image,
			Tier:     args.Tier,
			Strategy: args.Strategy,
		})
		return updated, err
	}

	return updated, hub.Store.UpsertApp(ctx, store.App{
		Owner:           userID,
		Name:            args.Name,
		Image:           args.Image,
		Tier:            args.Tier,
		SessionStrategy: args.Strategy,
	})
}

func printDeployOK(t *term, args DeployArgs, hub *Hub, ctx context.Context, userID string, updated, waitEnter bool) {
	verb := "Created"
	if updated {
		verb = "Updated"
	}
	app, _ := hub.Store.GetApp(ctx, userID, args.Name)
	t.Printf("\n✓ %s %s (%s)\n", verb, args.Name, args.Tier)
	t.Printf("  image:    %s\n", args.Image)
	t.Printf("  strategy: %s\n", strategyLabel(args.Strategy))
	if app != nil && app.ActiveGen != "" {
		t.Printf("  generation: %s\n", app.ActiveGen)
		if app.DrainingGen != "" {
			t.Printf("  draining:   %s\n", displayGen(app.DrainingGen))
		}
	}
	if hub.Cutover == nil {
		t.Printf("\nNote: instance cutover is not attached in this gateway process.\n")
	}
	t.Printf("\nConnect with:\n")
	t.Printf("  ssh %s@<host>\n", args.Name)
	if waitEnter {
		t.Printf("\nPress enter to return.\n")
		_, _ = t.ReadLine()
	}
}

func displayGen(gen string) string {
	if gen == "" {
		return "(legacy)"
	}
	return gen
}

func splitArgs(cmd string) []string {
	return strings.Fields(cmd)
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
