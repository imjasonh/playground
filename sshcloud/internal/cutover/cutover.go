// Package cutover implements deploy session strategies (drain / kick).
package cutover

import (
	"context"
	"fmt"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// DefaultDrainTimeout is the v1 drain-then-kick window.
const DefaultDrainTimeout = 5 * time.Minute

// Instances boots/stops host-agent generations.
type Instances interface {
	Ensure(ctx context.Context, user, app, gen, image string, noIdle bool) error
	Stop(ctx context.Context, user, app, gen string) error
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
	}
}

// Request is one deploy cutover.
type Request struct {
	User     string
	App      string
	Image    string
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
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil || a == nil {
		return "", err
	}
	return a.ActiveGen, nil
}

// Deploy boots a new generation and applies kick or drain.
func (c *Controller) Deploy(ctx context.Context, req Request) (Result, error) {
	if req.User == "" || req.App == "" {
		return Result{}, fmt.Errorf("user and app required")
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

	app, err := c.Store.GetApp(ctx, req.User, req.App)
	if err != nil {
		return Result{}, err
	}
	if app == nil {
		return Result{}, fmt.Errorf("unknown app %q", req.App)
	}

	oldGen := app.ActiveGen
	prevDraining := app.DrainingGen
	newGen := genid.New()

	if c.Instances != nil {
		if err := c.Instances.Ensure(ctx, req.User, req.App, newGen, req.Image, true); err != nil {
			return Result{}, fmt.Errorf("boot new generation: %w", err)
		}
	}

	switch strategy {
	case store.StrategyKick:
		c.kickGen(req.User, req.App, oldGen)
		if prevDraining != "" && prevDraining != oldGen {
			c.kickGen(req.User, req.App, prevDraining)
			if c.Instances != nil {
				_ = c.Instances.Stop(ctx, req.User, req.App, prevDraining)
			}
		}
		if c.Instances != nil {
			_ = c.Instances.Stop(ctx, req.User, req.App, oldGen)
		}
		return c.persistActive(ctx, app, req, newGen, strategy)

	default: // drain
		oldHasSession := c.Sessions != nil && c.Sessions.ActiveGen(req.User, req.App, oldGen)
		if !oldHasSession {
			if c.Instances != nil {
				_ = c.Instances.Stop(ctx, req.User, req.App, oldGen)
			}
			if prevDraining != "" && prevDraining != oldGen && c.Instances != nil {
				_ = c.Instances.Stop(ctx, req.User, req.App, prevDraining)
			}
			return c.persistActive(ctx, app, req, newGen, strategy)
		}

		app.PreviousImage = app.Image
		if req.Image != "" {
			app.Image = req.Image
		}
		app.ActiveGen = newGen
		app.DrainingGen = oldGen
		drainUntil := c.now().Add(timeout)
		app.DrainUntilUnix = drainUntil.Unix()
		app.SessionStrategy = strategy
		if err := c.Store.UpsertApp(ctx, *app); err != nil {
			return Result{}, err
		}
		if c.Instances != nil {
			_ = c.Instances.Ensure(ctx, req.User, req.App, oldGen, "", true)
		}
		c.armDrainTimer(req.User, req.App, drainUntil)
		return Result{ActiveGen: newGen, DrainingGen: oldGen, Strategy: strategy, DrainUntil: drainUntil}, nil
	}
}

func (c *Controller) persistActive(ctx context.Context, app *store.App, req Request, newGen, strategy string) (Result, error) {
	app.PreviousImage = app.Image
	if req.Image != "" {
		app.Image = req.Image
	}
	app.ActiveGen = newGen
	app.DrainingGen = ""
	app.DrainUntilUnix = 0
	app.SessionStrategy = strategy
	if err := c.Store.UpsertApp(ctx, *app); err != nil {
		return Result{}, err
	}
	if c.Instances != nil {
		_ = c.Instances.Ensure(ctx, req.User, req.App, newGen, req.Image, false)
	}
	c.clearTimer(req.User, req.App)
	return Result{ActiveGen: newGen, Strategy: strategy}, nil
}

// OnRelease is called after a session ends. Finishes drain if that gen is empty.
func (c *Controller) OnRelease(ctx context.Context, user, app, gen string) {
	if c == nil || c.Store == nil {
		return
	}
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil || a == nil {
		return
	}
	if a.DrainingGen == "" && a.DrainUntilUnix == 0 {
		return
	}
	if gen != a.DrainingGen {
		return
	}
	if c.Sessions != nil && c.Sessions.ActiveGen(user, app, gen) {
		return
	}
	c.finishDrain(ctx, user, app, gen)
}

func (c *Controller) finishDrain(ctx context.Context, user, app, gen string) {
	a, err := c.Store.GetApp(ctx, user, app)
	if err != nil || a == nil {
		return
	}
	if c.Instances != nil {
		_ = c.Instances.Stop(ctx, user, app, gen)
	}
	a.DrainingGen = ""
	a.DrainUntilUnix = 0
	_ = c.Store.UpsertApp(ctx, *a)
	if c.Instances != nil && a.ActiveGen != "" {
		_ = c.Instances.Ensure(ctx, user, app, a.ActiveGen, a.Image, false)
	}
	c.clearTimer(user, app)
}

func (c *Controller) kickGen(user, app, gen string) {
	if c.Sessions == nil {
		return
	}
	c.Sessions.Kick(user, app, gen)
}

func (c *Controller) armDrainTimer(user, app string, until time.Time) {
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
		a, err := c.Store.GetApp(ctx, user, app)
		if err != nil || a == nil {
			return
		}
		gen := a.DrainingGen
		c.kickGen(user, app, gen)
		time.Sleep(50 * time.Millisecond)
		c.finishDrain(ctx, user, app, gen)
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
