// Package gateway contains the SSH hub state machine (routing + admission).
// The cmd/gateway binary will speak SSH and call into this package.
package gateway

import (
	"context"
	"errors"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/route"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// Action is what the SSH layer should present after routing + admission.
type Action int

const (
	ActionJoin Action = iota
	ActionMenu
	ActionDeploy
	ActionProxyApp
	ActionRejectBusy
)

func (a Action) String() string {
	switch a {
	case ActionJoin:
		return "join"
	case ActionMenu:
		return "menu"
	case ActionDeploy:
		return "deploy"
	case ActionProxyApp:
		return "proxy_app"
	case ActionRejectBusy:
		return "reject_busy"
	default:
		return "unknown"
	}
}

// Result is the outcome of HandleConnect.
type Result struct {
	Action  Action
	User    string // set when key is known (or after join — caller updates)
	App     string // set for ActionProxyApp / ActionRejectBusy
	Session session.ID
	Message string
}

// Hub wires store + session registry for one gateway process.
type Hub struct {
	Store    store.Store
	Sessions *session.Registry
}

// Connect is the inbound connection facts after SSH key auth attempt.
type Connect struct {
	SSHUser         string
	KeyFingerprint  string
}

// HandleConnect routes and (for apps) admits a session.
// Caller must Release Result.Session when the SSH connection ends (if non-empty).
func (h *Hub) HandleConnect(ctx context.Context, c Connect) (Result, error) {
	user, err := h.Store.LookupUserByKey(ctx, c.KeyFingerprint)
	if err != nil {
		return Result{}, err
	}
	keyKnown := user != nil
	var userID string
	if keyKnown {
		userID = user.ID
	}

	hasApp := func(app string) bool {
		if store.IsPlatformDemo(app) {
			return true // deep link / menu may lazy-create
		}
		ok, err := h.Store.HasApp(ctx, userID, app)
		return err == nil && ok
	}

	d := route.Resolve(route.Input{
		SSHUser:  c.SSHUser,
		KeyKnown: keyKnown,
		HasApp:   hasApp,
	})

	switch d.Kind {
	case route.Join:
		return Result{Action: ActionJoin, User: userID}, nil
	case route.Menu:
		return Result{Action: ActionMenu, User: userID}, nil
	case route.Deploy:
		return Result{Action: ActionDeploy, User: userID}, nil
	case route.App:
		if err := h.maybeEnsureDemo(ctx, userID, d.App); err != nil {
			return Result{}, err
		}
		id, err := h.Sessions.Admit(userID, d.App)
		if err != nil {
			var busy session.ErrBusy
			if errors.As(err, &busy) {
				return Result{
					Action:  ActionRejectBusy,
					User:    userID,
					App:     d.App,
					Message: busy.Error(),
				}, nil
			}
			return Result{}, err
		}
		return Result{
			Action:  ActionProxyApp,
			User:    userID,
			App:     d.App,
			Session: id,
		}, nil
	default:
		return Result{}, fmt.Errorf("unhandled route kind %v", d.Kind)
	}
}

func (h *Hub) maybeEnsureDemo(ctx context.Context, userID, app string) error {
	if !store.IsPlatformDemo(app) {
		return nil
	}
	return h.Store.EnsureDemoApp(ctx, userID, app)
}

// ReleaseSession ends an admitted app session.
func (h *Hub) ReleaseSession(id session.ID) {
	if id != "" {
		h.Sessions.Release(id)
	}
}
