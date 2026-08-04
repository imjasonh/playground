package gateway

import (
	"context"
	"errors"
	"fmt"
	"io"
	"math/rand"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/session"
)

var errBackendMigration = errors.New("backend migration freeze")

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
		commands := make(chan session.MigrationCommand, 2)
		frozen := hub.BindMigration(res.Session, commands)
		for {
			if frozen {
				t.Printf("\n[sshcloud] host migration in progress; input is temporarily buffered\n")
				if !waitForThaw(ctx, commands) {
					return 1
				}
				t.Printf("[sshcloud] migration complete; reconnecting app session\n")
				frozen = false
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
			proxyCtx, cancelProxy := context.WithCancelCause(ctx)
			proxyDone := make(chan error, 1)
			go func() {
				proxyDone <- ProxySSH(proxyCtx, t.rw, hub.UserCA, res.User, addr)
			}()
		waitProxy:
			for {
				select {
				case err := <-proxyDone:
					cancelProxy(nil)
					return proxyExitCode(ctx, t, err)
				case command := <-commands:
					if command.Kind != session.MigrationFreeze {
						command.Ack <- fmt.Errorf("cannot %s an active backend session", command.Kind)
						continue
					}
					cancelProxy(errBackendMigration)
					<-proxyDone
					command.Ack <- nil
					frozen = true
					break waitProxy
				case <-ctx.Done():
					cancelProxy(context.Cause(ctx))
					<-proxyDone
					return 1
				}
			}
		}
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

func waitForThaw(ctx context.Context, commands <-chan session.MigrationCommand) bool {
	for {
		select {
		case command := <-commands:
			switch command.Kind {
			case session.MigrationThaw:
				command.Ack <- nil
				return true
			case session.MigrationFreeze:
				command.Ack <- nil
			default:
				command.Ack <- fmt.Errorf("unknown migration command %q", command.Kind)
			}
		case <-ctx.Done():
			return false
		}
	}
}

func proxyExitCode(ctx context.Context, t *term, err error) int {
	if err == nil {
		return 0
	}
	if ctx.Err() != nil {
		return 1
	}
	t.Printf("proxy error: %v\n", err)
	if exitErr, ok := err.(*ssh.ExitError); ok {
		return exitErr.ExitStatus()
	}
	return 1
}
