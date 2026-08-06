package gateway

import (
	"context"
	"errors"
	"fmt"
	"math/rand"

	"github.com/imjasonh/playground/sshcloud/internal/session"
)

var errBackendMigration = errors.New("backend migration freeze")

type proxyResult struct {
	exit AppExit
	err  error
}

var fortunes = []string{
	"The only way to do great work is to love what you do.",
	"ssh more, click less.",
	"MicroVMs are just very small computers with trust issues.",
	"Your future holds a short-lived SSH certificate.",
	"Fortune favors the joined.",
}

func RunAppSession(ctx context.Context, client ClientSession, hub *Hub, res Result) AppExit {
	return runAppSession(ctx, newSessionTerm(client), hub, res)
}

func runAppSession(ctx context.Context, t *term, hub *Hub, res Result) AppExit {
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
		input := t.beginProxy()
		defer t.endProxy()
		expectedHostKey := ""
		for {
			var thawAck chan error
			if frozen {
				t.Printf("\n[sshcloud] host migration in progress; input is temporarily buffered\n")
				thawed, overflow, changeErr, ack := waitForThaw(ctx, commands, input.Overflow(), t.client.Spec)
				thawAck = ack
				if changeErr != nil {
					fmt.Fprintf(t.client.Stderr, "%v\r\n", changeErr)
					return AppExit{Code: 255}
				}
				if overflow {
					t.Printf("[sshcloud] session closed: migration input buffer exceeded %d bytes\n", defaultMigrationBufferBytes)
					return AppExit{Code: 1}
				}
				if !thawed {
					return AppExit{Code: 1}
				}
				frozen = false
			}

			request := DialRequest{
				User:      res.User,
				App:       res.App,
				Gen:       res.Gen,
				Image:     img,
				Tier:      tier,
				NoIdle:    true,
				Purpose:   "session",
				RequestID: string(res.Session),
			}
			var target DialTarget
			var err error
			if t.client.Spec.Migratable() {
				target, err = DialWithLoading(ctx, t.out, res.App, hub.Dial, request)
			} else {
				target, err = hub.Dial(ctx, request)
			}
			if err != nil {
				if thawAck != nil {
					thawAck <- err
				}
				t.client.Spec.ReplyStart(false)
				fmt.Fprintf(t.client.Stderr, "backend error: %v\r\n", err)
				return AppExit{Code: 1}
			}
			if expectedHostKey == "" {
				expectedHostKey = target.SSHHostPublicKey
			} else if target.SSHHostPublicKey != expectedHostKey {
				if thawAck != nil {
					thawAck <- fmt.Errorf("backend host key changed during migration")
				}
				fmt.Fprint(t.client.Stderr, "backend host key changed during migration\r\n")
				return AppExit{Code: 1}
			}
			proxyCtx, cancelProxy := context.WithCancelCause(ctx)
			proxyDone := make(chan proxyResult, 1)
			var ready chan error
			if thawAck != nil {
				ready = make(chan error, 1)
			}
			attachment := input.Attach()
			go func() {
				exit, err := ProxySSHStreams(
					proxyCtx, attachment, t.rw, t.client.Stderr,
					hub.UserCA, res.User, target, t.client.Spec, ready,
				)
				proxyDone <- proxyResult{exit: exit, err: err}
			}()
			if thawAck != nil {
				select {
				case readyErr := <-ready:
					thawAck <- readyErr
					if readyErr != nil {
						_ = attachment.Close()
						result := <-proxyDone
						cancelProxy(nil)
						return proxyExit(ctx, t, result)
					}
					t.Printf("[sshcloud] migration complete; app session reconnected\n")
				case <-ctx.Done():
					thawAck <- ctx.Err()
					cancelProxy(context.Cause(ctx))
					_ = attachment.Close()
					<-proxyDone
					return AppExit{Code: 1}
				}
			}
		waitProxy:
			for {
				select {
				case result := <-proxyDone:
					_ = attachment.Close()
					cancelProxy(nil)
					return proxyExit(ctx, t, result)
				case command := <-commands:
					if command.Kind != session.MigrationFreeze {
						command.Ack <- fmt.Errorf("cannot %s an active backend session", command.Kind)
						continue
					}
					if !t.client.Spec.Migratable() {
						cancelProxy(errors.New("non-interactive session cannot migrate"))
						_ = attachment.Close()
						<-proxyDone
						command.Ack <- nil
						return AppExit{Code: 255}
					}
					cancelProxy(errBackendMigration)
					_ = attachment.Close()
					<-proxyDone
					command.Ack <- nil
					frozen = true
					break waitProxy
				case <-ctx.Done():
					cancelProxy(context.Cause(ctx))
					_ = attachment.Close()
					<-proxyDone
					return AppExit{Code: 1}
				case <-input.Overflow():
					cancelProxy(fmt.Errorf("migration input buffer exceeded %d bytes", defaultMigrationBufferBytes))
					_ = attachment.Close()
					<-proxyDone
					t.Printf("\n[sshcloud] session closed: migration input buffer exceeded %d bytes\n", defaultMigrationBufferBytes)
					return AppExit{Code: 1}
				}
			}
		}
	}

	// Local demonstration fallback when no CA/backend is configured.
	if t.client.Spec.StartType != SessionShell {
		t.client.Spec.ReplyStart(true)
		fmt.Fprint(t.client.Stderr, "app backend is not configured\r\n")
		return AppExit{Code: 1}
	}
	t.client.Spec.ReplyStart(true)
	t.Printf("app %q: no backend configured\n", res.App)
	t.Printf("(deploy a digest-pinned image and run gateway with -agent-url)\n")
	if res.App == "fortune" {
		t.Printf("\n── sample fortune ──\n")
		t.Printf("%s\n", fortunes[rand.Intn(len(fortunes))])
		t.Printf("───────────────────\n")
	}
	t.Printf("Press enter to return.\n")
	_, _ = t.ReadLine()
	return AppExit{Code: 0}
}

func waitForThaw(ctx context.Context, commands <-chan session.MigrationCommand, overflow <-chan struct{}, spec *SessionSpec) (bool, bool, error, chan error) {
	changes := spec.Changes
	for {
		select {
		case command := <-commands:
			switch command.Kind {
			case session.MigrationThaw:
				return true, false, nil, command.Ack
			case session.MigrationFreeze:
				command.Ack <- nil
			default:
				command.Ack <- fmt.Errorf("unknown migration command %q", command.Kind)
			}
		case <-ctx.Done():
			return false, false, nil, nil
		case <-overflow:
			return false, true, nil, nil
		case change, ok := <-changes:
			if ok {
				if err := spec.RecordDetachedChange(change); err != nil {
					return false, false, err, nil
				}
			} else {
				changes = nil
			}
		}
	}
}

func proxyExit(ctx context.Context, t *term, result proxyResult) AppExit {
	if result.err == nil {
		return result.exit
	}
	if ctx.Err() != nil {
		return AppExit{Code: 1}
	}
	fmt.Fprintf(t.client.Stderr, "proxy error: %v\r\n", result.err)
	return AppExit{Code: 1}
}
