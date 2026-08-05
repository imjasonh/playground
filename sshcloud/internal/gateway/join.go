package gateway

import (
	"context"
	"io"
	"strings"

	"github.com/imjasonh/playground/sshcloud/internal/names"
)

// RunJoin handles onboarding (unknown key) or key management (known user).
// When execCmd is set for a new user (`ssh join@host demo`), joins
// non-interactively and returns an exit code (0 ok, 1 failure).
func RunJoin(ctx context.Context, ch io.ReadWriter, hub *Hub, keyFP, userID, execCmd string) int {
	return RunJoinSession(ctx, ClientSession{IO: ch, Stderr: ch, Spec: &SessionSpec{StartType: SessionShell, PTY: true}}, hub, keyFP, userID, execCmd)
}

func RunJoinSession(ctx context.Context, client ClientSession, hub *Hub, keyFP, userID, execCmd string) int {
	t := newSessionTerm(client)
	if userID == "" {
		return runJoinNew(ctx, t, hub, keyFP, execCmd)
	}
	if strings.TrimSpace(execCmd) != "" {
		fields := strings.Fields(execCmd)
		if len(fields) != 1 || fields[0] != userID {
			t.Printf("This key is already registered as %s; requested username must match.\n", userID)
			return 2
		}
		t.Printf("Already joined as %s\n", userID)
		return 0
	}
	runJoinManage(t, userID, keyFP)
	return 0
}

func runJoinNew(ctx context.Context, t *term, hub *Hub, keyFP, execCmd string) int {
	execCmd = strings.TrimSpace(execCmd)
	if execCmd != "" {
		fields := strings.Fields(execCmd)
		if len(fields) != 1 {
			t.Printf("Usage: ssh join@host <username>\n")
			return 2
		}
		name := fields[0]
		if err := names.ValidateIdent(name); err != nil {
			t.Printf("Invalid username: %v\n", err)
			return 1
		}
		if err := hub.Store.CreateUser(ctx, name, keyFP); err != nil {
			t.Printf("Could not create user: %v\n", err)
			return 1
		}
		t.Printf("Joined as %s\n", name)
		t.Printf("Key %s\n", keyFP)
		return 0
	}

	t.Printf("Welcome to SSH App Cloud\n")
	t.Printf("Found key %s\n\n", keyFP)
	for {
		t.Printf("Pick a username: ")
		name, err := t.ReadLine()
		if err != nil {
			return 1
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
		return 0
	}
}

func runJoinManage(t *term, userID, keyFP string) {
	t.Printf("Logged in as %s\n", userID)
	t.Printf("This key: %s\n", keyFP)
	t.Printf("\nKey management is limited in this build.\n")
	t.Printf("To add another key, authenticate with an existing key (more UX later).\n")
	t.Printf("Try: ssh menu@<host> or ssh deploy@<host>\n")
}
