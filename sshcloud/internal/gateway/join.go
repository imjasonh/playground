package gateway

import (
	"context"
	"io"

	"github.com/imjasonh/playground/sshcloud/internal/names"
)

// RunJoin handles onboarding (unknown key) or key management (known user).
func RunJoin(ctx context.Context, ch io.ReadWriter, hub *Hub, keyFP, userID string) {
	t := newTerm(ch)
	if userID == "" {
		runJoinNew(ctx, t, hub, keyFP)
		return
	}
	runJoinManage(t, userID, keyFP)
}

func runJoinNew(ctx context.Context, t *term, hub *Hub, keyFP string) {
	t.Printf("Welcome to SSH App Cloud\n")
	t.Printf("Found key %s\n\n", keyFP)
	for {
		t.Printf("Pick a username: ")
		name, err := t.ReadLine()
		if err != nil {
			return
		}
		if err := names.ValidateIdent(name); err != nil {
			t.Printf("Invalid: %v\n", err)
			continue
		}
		if err := hub.Store.CreateUser(ctx, name, keyFP); err != nil {
			t.Printf("Could not create user: %v\n", err)
			continue
		}
		t.Printf("\nYou're %s. Opening app menu…\n\n", name)
		// Reuse the same term so a buffered stdin (e.g. scripted tests)
		// is not lost when opening the menu.
		runMenu(ctx, t, hub, keyFP, name)
		return
	}
}

func runJoinManage(t *term, userID, keyFP string) {
	t.Printf("Logged in as %s\n", userID)
	t.Printf("This key: %s\n", keyFP)
	t.Printf("\nKey management is limited in this build.\n")
	t.Printf("To add another key, authenticate with an existing key (more UX later).\n")
	t.Printf("Try: ssh menu@<host> or ssh deploy@<host>\n")
}
