// Package gateway contains the SSH hub state machine (routing + admission).
// The cmd/gateway binary will speak SSH and call into this package.
package gateway

import (
	"context"
	"errors"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/route"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
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
	Gen     string // microVM generation this session is pinned to
	Image   string // immutable deploy spec pinned with Gen
	Tier    string
	Session session.ID
	Message string
}

// Hub wires store + session registry for one gateway process.
type Hub struct {
	Store    store.Store
	Sessions *session.Registry
	UserCA   *userca.CA // optional; when set with Dial, apps are proxied over SSH
	Dial     DialFunc   // optional backend address resolver
	Cutover  *cutover.Controller
	// AllowedRegistries mirrors the agent-side SSRF boundary for immediate
	// deploy feedback. Empty is local-dev only.
	AllowedRegistries []string
}

// Connect is the inbound connection facts after SSH key auth attempt.
type Connect struct {
	SSHUser        string
	KeyFingerprint string
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

	var routeErr error
	hasApp := func(app string) bool {
		ok, err := h.Store.HasApp(ctx, userID, app)
		if err != nil {
			routeErr = err
			return false
		}
		return ok
	}

	d := route.Resolve(route.Input{
		SSHUser:  c.SSHUser,
		KeyKnown: keyKnown,
		HasApp:   hasApp,
	})
	if routeErr != nil {
		return Result{}, fmt.Errorf("resolve app route: %w", routeErr)
	}

	switch d.Kind {
	case route.Join:
		return Result{Action: ActionJoin, User: userID}, nil
	case route.Menu:
		return Result{Action: ActionMenu, User: userID}, nil
	case route.Deploy:
		return Result{Action: ActionDeploy, User: userID}, nil
	case route.App:
		return h.admitApp(ctx, userID, d.App)
	default:
		return Result{}, fmt.Errorf("unhandled route kind %v", d.Kind)
	}
}

func (h *Hub) admitApp(ctx context.Context, userID, app string) (Result, error) {
	var (
		id          session.ID
		gen         string
		pinnedImage string
		pinnedTier  string
		err         error
	)
	if h.Cutover != nil {
		id, gen, pinnedImage, pinnedTier, err = h.Cutover.Admit(ctx, userID, app)
	} else {
		var pinned *store.App
		pinned, err = h.Store.GetApp(ctx, userID, app)
		if err == nil && pinned == nil {
			err = fmt.Errorf("unknown app %q", app)
		}
		if err == nil {
			gen, pinnedImage, pinnedTier = pinned.ActiveGen, pinned.Image, pinned.Tier
			id, err = h.Sessions.Admit(userID, app, gen)
		}
	}
	if err != nil {
		var busy session.ErrBusy
		if errors.As(err, &busy) {
			return Result{
				Action:  ActionRejectBusy,
				User:    userID,
				App:     app,
				Gen:     gen,
				Message: busy.Error(),
			}, nil
		}
		return Result{}, err
	}
	return Result{
		Action:  ActionProxyApp,
		User:    userID,
		App:     app,
		Gen:     gen,
		Image:   pinnedImage,
		Tier:    pinnedTier,
		Session: id,
	}, nil
}

// ReleaseSession ends an admitted app session and may complete a drain.
func (h *Hub) ReleaseSession(id session.ID) {
	if id == "" {
		return
	}
	user, app, gen, ok := h.Sessions.Info(id)
	h.Sessions.Release(id)
	if ok && h.Cutover != nil {
		h.Cutover.OnRelease(context.Background(), user, app, gen)
	}
}

// BindSession returns a cancelable context for a proxied session (deploy kick).
func (h *Hub) BindSession(parent context.Context, id session.ID) (context.Context, context.CancelFunc) {
	if parent == nil {
		parent = context.Background()
	}
	ctx, cancel := context.WithCancel(parent)
	if id != "" && h.Sessions != nil {
		h.Sessions.BindCancel(id, cancel)
	}
	return ctx, cancel
}

// BindMigration attaches host-migration commands to a proxied session.
func (h *Hub) BindMigration(id session.ID, commands chan session.MigrationCommand) bool {
	if h == nil || h.Sessions == nil {
		return false
	}
	return h.Sessions.BindMigration(id, commands)
}

// FreezeApp disconnects a backend hop while preserving the outer SSH session.
func (h *Hub) FreezeApp(ctx context.Context, user, app, gen string) (int, error) {
	return h.Sessions.Freeze(ctx, user, app, gen)
}

// ThawApp lets a frozen session reconnect through current placement.
func (h *Hub) ThawApp(ctx context.Context, user, app, gen string) (int, error) {
	return h.Sessions.Thaw(ctx, user, app, gen)
}

// KickApp terminates matching outer sessions.
func (h *Hub) KickApp(user, app, gen string) int {
	return h.Sessions.Kick(user, app, gen)
}

func (h *Hub) SessionIDs(user, app, gen string) []session.ID {
	return h.Sessions.MatchingIDs(user, app, gen)
}

func (h *Hub) FreezeSessions(ctx context.Context, ids []session.ID) error {
	return h.Sessions.FreezeIDs(ctx, ids)
}

func (h *Hub) ThawSessions(ctx context.Context, ids []session.ID) error {
	return h.Sessions.ThawIDs(ctx, ids)
}

func (h *Hub) KickSessions(ids []session.ID) int {
	return h.Sessions.KickIDs(ids)
}

// OpenApp admits a session for an already-authenticated user and existing app.
// Used by the in-session menu handoff (key auth already happened on the SSH conn).
func (h *Hub) OpenApp(ctx context.Context, userID, app string) (Result, error) {
	if userID == "" || app == "" {
		return Result{}, fmt.Errorf("user and app required")
	}
	ok, err := h.Store.HasApp(ctx, userID, app)
	if err != nil {
		return Result{}, err
	}
	if !ok {
		return Result{}, fmt.Errorf("unknown app %q — deploy it first", app)
	}
	return h.admitApp(ctx, userID, app)
}
