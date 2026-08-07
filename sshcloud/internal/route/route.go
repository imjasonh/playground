// Package route decides what the SSH gateway should do for a connection.
//
// See docs/ssh-app-cloud-design.md §3 (SSH username routing).
package route

import "github.com/imjasonh/playground/sshcloud/internal/names"

// Kind is the high-level gateway action for a connection.
type Kind int

const (
	// Join shows the onboarding / key-management TUI.
	Join Kind = iota
	// Menu shows the app picker (hub).
	Menu
	// Deploy shows the deploy TUI.
	Deploy
	// App deep-links (or hands off) to a user app.
	App
)

func (k Kind) String() string {
	switch k {
	case Join:
		return "join"
	case Menu:
		return "menu"
	case Deploy:
		return "deploy"
	case App:
		return "app"
	default:
		return "unknown"
	}
}

// Decision is the routing result for one SSH user field + auth state.
type Decision struct {
	Kind Kind
	// App is set when Kind == App (the app name in the user's namespace).
	App string
}

// Input is everything needed to route a connection (no I/O).
type Input struct {
	// SSHUser is the username field from the client (local account for bare ssh host).
	SSHUser string
	// KeyKnown is true when the presenting key maps to a registered user.
	KeyKnown bool
	// HasApp reports whether the registered user already has this app.
	// Ignored if KeyKnown is false.
	HasApp func(app string) bool
}

// Resolve applies the design routing rules.
func Resolve(in Input) Decision {
	if !in.KeyKnown {
		return Decision{Kind: Join}
	}

	user := in.SSHUser
	switch user {
	case "join":
		return Decision{Kind: Join}
	case "deploy":
		return Decision{Kind: Deploy}
	case "menu", "":
		return Decision{Kind: Menu}
	}

	if names.IsReserved(user) {
		// help/status/whoami/root/admin — not implemented; fall through to menu.
		return Decision{Kind: Menu}
	}

	has := false
	if in.HasApp != nil {
		has = in.HasApp(user)
	}
	if has {
		return Decision{Kind: App, App: user}
	}
	// Unknown app name (including bare ssh foo.com → local username) → hub.
	return Decision{Kind: Menu}
}
