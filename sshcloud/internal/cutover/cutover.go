// Package cutover implements deploy session strategies (drain / kick).
package cutover

import (
	"context"
	"fmt"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// DefaultDrainTimeout is the v1 drain-then-kick window.
const DefaultDrainTimeout = 5 * time.Minute

// Instances boots/stops host-agent generations.
type Instances interface {
	Ensure(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error
	Stop(ctx context.Context, user, app, gen string) error
	SetNoIdle(ctx context.Context, user, app, gen string, noIdle bool) error
}

// Controller coordinates routing + instance lifetime across a deploy.
type Controller struct {
	Store     store.Store
	Sessions  *session.Registry
	Instances Instances
	Timeout   time.Duration
	now       func() time.Time

	mu     sync.Mutex
	timers map[string]*time.Timer // user/app → drain deadline timer
	opMu   sync.Mutex
	ops    map[string]*sync.Mutex
}

// New returns a controller. instances may be nil (routing-only / tests).
func New(st store.Store, sess *session.Registry, instances Instances) *Controller {
	return &Controller{
		Store:     st,
		Sessions:  sess,
		Instances: instances,
		Timeout:   DefaultDrainTimeout,
		now:       time.Now,
		timers:    make(map[string]*time.Timer),
		ops:       make(map[string]*sync.Mutex),
	}
}

// Request is one deploy cutover.
type Request struct {
	User     string
	App      string
	Image    string
	Tier     string
	Strategy string
	Timeout  time.Duration
}

// Result is persisted routing after Deploy.
type Result struct {
	ActiveGen   string
	DrainingGen string
	Strategy    string
	DrainUntil  time.Time
}

// ActiveGen is what new sessions should pin to (empty = legacy singleton).
func (c *Controller) ActiveGen(ctx context.Context, user, app string) (string, error) {
	if c == nil || c.Store == nil {
		return "", nil
	}
	op := c.appLock(user, app)
	op.Lock()
	defer op.Unlock()
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil || a == nil {
		return "", err
	}
	if a.DrainingGen != "" && a.DrainUntilUnix > 0 && c.now().Unix() >= a.DrainUntilUnix {
		c.kickGen(user, app, a.DrainingGen)
		c.finishDrainLocked(ctx, user, app, a.DrainingGen)
		a, err = c.Store.GetApp(ctx, user, app)
		if err != nil || a == nil {
			return "", err
		}
	} else if a.DrainingGen != "" && a.DrainUntilUnix > 0 {
		c.armDrainTimer(user, app, a.DrainingGen, time.Unix(a.DrainUntilUnix, 0))
	}
	return a.ActiveGen, nil
}

// Admit atomically pins and registers a session against the active generation.
// It shares the per-app operation lock with Deploy so no connection can be
// admitted to a generation while cutover is publishing another.
func (c *Controller) Admit(ctx context.Context, user, app string) (session.ID, string, error) {
	if c == nil || c.Store == nil || c.Sessions == nil {
		return "", "", fmt.Errorf("cutover admission is not configured")
	}
	op := c.appLock(user, app)
	op.Lock()
	defer op.Unlock()
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil {
		return "", "", err
	}
	if a == nil {
		return "", "", fmt.Errorf("unknown app %q", app)
	}
	if a.DrainingGen != "" && a.DrainUntilUnix > 0 {
		if c.now().Unix() >= a.DrainUntilUnix {
			c.kickGen(user, app, a.DrainingGen)
			c.finishDrainLocked(ctx, user, app, a.DrainingGen)
			a, err = c.Store.GetApp(ctx, user, app)
			if err != nil {
				return "", "", err
			}
			if a == nil {
				return "", "", fmt.Errorf("app %q disappeared during drain cleanup", app)
			}
		} else {
			c.armDrainTimer(user, app, a.DrainingGen, time.Unix(a.DrainUntilUnix, 0))
		}
	}
	id, err := c.Sessions.Admit(user, app, a.ActiveGen)
	return id, a.ActiveGen, err
}

func (c *Controller) appLock(user, app string) *sync.Mutex {
	key := user + "/" + app
	c.opMu.Lock()
	defer c.opMu.Unlock()
	op := c.ops[key]
	if op == nil {
		op = &sync.Mutex{}
		c.ops[key] = op
	}
	return op
}

// Deploy boots a new generation and applies kick or drain.
func (c *Controller) Deploy(ctx context.Context, req Request) (Result, error) {
	if req.User == "" || req.App == "" {
		return Result{}, fmt.Errorf("user and app required")
	}
	if err := image.ValidateDigestPinned(req.Image); err != nil {
		return Result{}, err
	}
	if req.Tier == "" {
		req.Tier = "tiny"
	}
	if req.Tier != "tiny" && req.Tier != "small" {
		return Result{}, fmt.Errorf("unknown tier %q", req.Tier)
	}
	strategy := req.Strategy
	if strategy == "" {
		strategy = store.StrategyDrain
	}
	if strategy != store.StrategyDrain && strategy != store.StrategyKick {
		return Result{}, fmt.Errorf("unknown strategy %q", strategy)
	}
	timeout := req.Timeout
	if timeout <= 0 {
		timeout = c.Timeout
		if timeout <= 0 {
			timeout = DefaultDrainTimeout
		}
	}

	op := c.appLock(req.User, req.App)
	op.Lock()
	defer op.Unlock()

	app, err := c.Store.GetApp(ctx, req.User, req.App)
	if err != nil {
		return Result{}, err
	}
	if app == nil {
		app = &store.App{Owner: req.User, Name: req.App}
	}
	if app.DrainingGen != "" && app.DrainUntilUnix > 0 && c.now().Unix() >= app.DrainUntilUnix {
		c.kickGen(req.User, req.App, app.DrainingGen)
		c.finishDrainLocked(ctx, req.User, req.App, app.DrainingGen)
		app, err = c.Store.GetApp(ctx, req.User, req.App)
		if err != nil {
			return Result{}, err
		}
		if app == nil {
			return Result{}, fmt.Errorf("app %q disappeared during drain cleanup", req.App)
		}
	}
	if app.DrainingGen != "" {
		return Result{}, fmt.Errorf("app %q is still draining generation %s; wait for it to finish before deploying again", req.App, app.DrainingGen)
	}
	if app.ActiveGen != "" && app.Image == req.Image && app.Tier == req.Tier {
		if c.Instances != nil {
			hold := c.Sessions != nil && c.Sessions.ActiveGen(req.User, req.App, app.ActiveGen)
			if err := c.Instances.Ensure(ctx, req.User, req.App, app.ActiveGen, app.Image, app.Tier, hold); err != nil {
				return Result{}, fmt.Errorf("verify active generation: %w", err)
			}
		}
		app.SessionStrategy = strategy
		if err := c.Store.UpsertApp(ctx, *app); err != nil {
			return Result{}, err
		}
		return Result{ActiveGen: app.ActiveGen, Strategy: strategy}, nil
	}

	oldGen := app.ActiveGen
	newGen := genid.New()

	if c.Instances != nil {
		if err := c.Instances.Ensure(ctx, req.User, req.App, newGen, req.Image, req.Tier, true); err != nil {
			return Result{}, fmt.Errorf("boot new generation: %w", err)
		}
	}

	persist := func(draining string, until time.Time) error {
		app.PreviousImage = app.Image
		app.Image = req.Image
		app.Tier = req.Tier
		app.ActiveGen = newGen
		app.DrainingGen = draining
		app.DrainUntilUnix = 0
		if !until.IsZero() {
			app.DrainUntilUnix = until.Unix()
		}
		app.SessionStrategy = strategy
		if err := c.Store.UpsertApp(ctx, *app); err != nil {
			if c.Instances != nil {
				_ = c.Instances.Stop(context.Background(), req.User, req.App, newGen)
			}
			return err
		}
		if c.Instances != nil {
			_ = c.Instances.SetNoIdle(ctx, req.User, req.App, newGen, false)
		}
		return nil
	}

	switch strategy {
	case store.StrategyKick:
		if err := persist("", time.Time{}); err != nil {
			return Result{}, err
		}
		c.kickGen(req.User, req.App, oldGen)
		if c.Instances != nil {
			_ = c.Instances.Stop(ctx, req.User, req.App, oldGen)
		}
		c.clearTimer(req.User, req.App)
		return Result{ActiveGen: newGen, Strategy: strategy}, nil

	default: // drain
		oldHasSession := c.Sessions != nil && c.Sessions.ActiveGen(req.User, req.App, oldGen)
		if !oldHasSession {
			if err := persist("", time.Time{}); err != nil {
				return Result{}, err
			}
			if c.Instances != nil {
				_ = c.Instances.Stop(ctx, req.User, req.App, oldGen)
			}
			c.clearTimer(req.User, req.App)
			return Result{ActiveGen: newGen, Strategy: strategy}, nil
		}

		drainUntil := c.now().Add(timeout)
		if c.Instances != nil {
			if err := c.Instances.SetNoIdle(ctx, req.User, req.App, oldGen, true); err != nil {
				_ = c.Instances.Stop(context.Background(), req.User, req.App, newGen)
				return Result{}, fmt.Errorf("hold draining generation awake: %w", err)
			}
		}
		if err := persist(oldGen, drainUntil); err != nil {
			return Result{}, err
		}
		c.armDrainTimer(req.User, req.App, oldGen, drainUntil)
		return Result{ActiveGen: newGen, DrainingGen: oldGen, Strategy: strategy, DrainUntil: drainUntil}, nil
	}
}

// OnRelease is called after a session ends. Finishes drain if that gen is empty.
func (c *Controller) OnRelease(ctx context.Context, user, app, gen string) {
	if c == nil || c.Store == nil {
		return
	}
	op := c.appLock(user, app)
	op.Lock()
	defer op.Unlock()
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil || a == nil {
		return
	}
	if gen == a.ActiveGen && (c.Sessions == nil || !c.Sessions.ActiveGen(user, app, gen)) && c.Instances != nil {
		_ = c.Instances.SetNoIdle(ctx, user, app, gen, false)
	}
	if a.DrainingGen == "" || gen != a.DrainingGen {
		return
	}
	if c.Sessions != nil && c.Sessions.ActiveGen(user, app, gen) {
		return
	}
	c.finishDrainLocked(ctx, user, app, gen)
}

func (c *Controller) finishDrainLocked(ctx context.Context, user, app, gen string) {
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil || a == nil {
		return
	}
	if a.DrainingGen != gen {
		return
	}
	a.DrainingGen = ""
	a.DrainUntilUnix = 0
	if err := c.Store.UpsertApp(ctx, *a); err != nil {
		return
	}
	if c.Instances != nil {
		_ = c.Instances.Stop(ctx, user, app, gen)
		if a.ActiveGen != "" && (c.Sessions == nil || !c.Sessions.ActiveGen(user, app, a.ActiveGen)) {
			_ = c.Instances.SetNoIdle(ctx, user, app, a.ActiveGen, false)
		}
	}
	c.clearTimer(user, app)
}

func (c *Controller) kickGen(user, app, gen string) {
	if c.Sessions == nil {
		return
	}
	c.Sessions.Kick(user, app, gen)
}

func (c *Controller) armDrainTimer(user, app, gen string, until time.Time) {
	if until.IsZero() {
		return
	}
	c.clearTimer(user, app)
	delay := time.Until(until)
	if delay < 0 {
		delay = 0
	}
	key := user + "/" + app
	c.mu.Lock()
	c.timers[key] = time.AfterFunc(delay, func() {
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		op := c.appLock(user, app)
		op.Lock()
		defer op.Unlock()
		a, err := c.Store.GetApp(ctx, user, app)
		if err != nil || a == nil || a.DrainingGen != gen || a.DrainUntilUnix != until.Unix() {
			return
		}
		c.kickGen(user, app, gen)
		c.finishDrainLocked(ctx, user, app, gen)
	})
	c.mu.Unlock()
}

func (c *Controller) clearTimer(user, app string) {
	key := user + "/" + app
	c.mu.Lock()
	if t := c.timers[key]; t != nil {
		t.Stop()
		delete(c.timers, key)
	}
	c.mu.Unlock()
}
