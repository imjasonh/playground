// Package ui runs the liquid simulation as a Bubble Tea program.
//
// The tank fills the terminal between a one-line header and a one-line
// toolbar. bubblezone marks the tank and each toolbar button as a zone, so a
// mouse event is mapped to a button, or to a point in the tank, by asking the
// zone manager rather than by recomputing the layout.
package ui

import (
	"math"
	"time"

	tea "charm.land/bubbletea/v2"
	zone "github.com/lrstanley/bubblezone/v2"

	"github.com/imjasonh/playground/liquid/internal/render"
	"github.com/imjasonh/playground/liquid/internal/sim"
)

// Options configures a Model.
type Options struct {
	Scene sim.Scene
	Theme *render.Theme
	Mode  render.Mode
	// Particles is roughly how many particles a scene starts with. The model
	// picks the size of a particle on screen to match.
	Particles int
	// FPS is how many frames per second the model simulates and draws.
	FPS  int
	Seed uint64
	// Now returns the current time. Tests replace it to control time.
	Now func() time.Time
}

// Brush sizes, in h.
const (
	defaultBrush = 3.4
	minBrush     = 1.2
	maxBrush     = 10.0
)

// referenceFill is the fraction of the tank used to pick the on-screen size
// of a particle. Every scene uses the same size, so the liquid looks the same
// in each one and only the particle count changes.
const referenceFill = 0.35

// maxStepsPerFrame bounds the simulation work per frame. If the machine can't
// keep up, the simulation slows down instead of falling further behind.
const maxStepsPerFrame = 12

// Model is the Bubble Tea model for the simulation.
type Model struct {
	opts  Options
	zones *zone.Manager
	world *sim.World
	rend  *render.Renderer
	st    styles

	width, height int     // Terminal size, in cells.
	cols, rows    int     // Tank size, in cells.
	scale         float64 // Pixels per h.

	scene     sim.Scene
	theme     int
	mode      render.Mode
	gravity   sim.Vec // Direction of gravity when it's on.
	gravityOn bool
	paused    bool
	help      bool
	hoverTool sim.Tool // Tool applied while hovering without a modifier.
	brush     float64  // Brush radius, in h.

	mouse       mouseState
	pressedZone string // Button under the cursor when the left button went down.
	hoverZone   string // Button under the cursor.

	lastTick   time.Time
	debt       float64 // Simulated time owed, in seconds.
	frames     int     // Frames since fpsSince.
	fpsSince   time.Time
	fps        float64
	stepMillis float64 // Smoothed simulation time per frame.
	hintUntil  time.Time

	frame string // The last rendered view, already scanned for zones.
	stale bool   // Whether frame needs to be rendered again.
}

type mouseState struct {
	over   bool    // Whether the cursor is over the tank.
	px, py float64 // Cursor position in pixels.
	button tea.MouseButton
	mod    tea.KeyMod
	at     time.Time // Time of the last mouse event.
	vel    sim.Vec   // Smoothed cursor velocity, in h/s.
}

type tickMsg time.Time

// New returns a model. It has no tank until it receives the terminal size.
func New(opts Options) *Model {
	if opts.Theme == nil {
		opts.Theme = render.Themes[0]
	}
	if opts.Particles <= 0 {
		opts.Particles = 2200
	}
	if opts.FPS <= 0 {
		opts.FPS = 60
	}
	if opts.Now == nil {
		opts.Now = time.Now
	}
	m := &Model{
		opts:      opts,
		zones:     zone.New(),
		rend:      render.New(),
		scene:     opts.Scene,
		mode:      opts.Mode,
		gravity:   sim.Vec{X: 0, Y: 1},
		gravityOn: true,
		brush:     defaultBrush,
		stale:     true,
	}
	for i, t := range render.Themes {
		if t == opts.Theme {
			m.theme = i
		}
	}
	m.st = newStyles(m.currentTheme())
	now := opts.Now()
	m.lastTick, m.fpsSince = now, now
	m.hintUntil = now.Add(8 * time.Second)
	return m
}

// Close stops the zone manager's background worker.
func (m *Model) Close() { m.zones.Close() }

// Init starts the frame clock.
func (m *Model) Init() tea.Cmd {
	return m.nextTick(0)
}

func (m *Model) nextTick(spent time.Duration) tea.Cmd {
	delay := time.Second/time.Duration(m.opts.FPS) - spent
	return tea.Tick(max(delay, time.Millisecond), func(t time.Time) tea.Msg { return tickMsg(t) })
}

// Update handles a message.
func (m *Model) Update(msg tea.Msg) (tea.Model, tea.Cmd) {
	switch msg := msg.(type) {
	case tea.WindowSizeMsg:
		m.resize(msg.Width, msg.Height)
	case tickMsg:
		start := time.Now()
		m.advance()
		return m, m.nextTick(time.Since(start))
	case tea.KeyPressMsg:
		return m, m.onKey(msg)
	case tea.MouseClickMsg:
		m.onMouseDown(msg)
	case tea.MouseReleaseMsg:
		return m, m.onMouseUp(msg)
	case tea.MouseMotionMsg:
		m.onMouseMove(msg)
	case tea.MouseWheelMsg:
		m.onWheel(msg)
	}
	return m, nil
}

// View returns the last rendered frame, rendering a new one first if the
// state changed. Bubble Tea calls View after every message, and mouse motion
// can arrive hundreds of times a second, so the simulation is only drawn once
// per tick.
func (m *Model) View() tea.View {
	if m.stale || m.frame == "" {
		m.frame = m.zones.Scan(m.compose())
		m.stale = false
	}
	v := tea.NewView(m.frame)
	v.AltScreen = true
	v.MouseMode = tea.MouseModeAllMotion
	v.WindowTitle = "liquid"
	return v
}

func (m *Model) currentTheme() *render.Theme { return render.Themes[m.theme] }

// resize lays out the screen for a terminal of the given size. The first call
// creates the tank. Later calls keep the liquid and move any particles that
// end up outside the tank back inside.
func (m *Model) resize(width, height int) {
	m.width, m.height = width, height
	m.cols = max(width-2, 0)
	m.rows = max(height-4, 0)
	m.stale = true
	if m.cols < minCols || m.rows < minRows {
		return
	}
	if m.world == nil {
		m.reset(m.scene)
		return
	}
	m.world.Resize(float64(m.cols)/m.scale, float64(m.rows*2)/m.scale)
	m.world.MaxParticles = m.maxParticles()
}

// reset fills the tank with a scene, picking the particle size so that the
// scene has about opts.Particles particles.
func (m *Model) reset(scene sim.Scene) {
	m.scene = scene
	pw, ph := float64(m.cols), float64(m.rows*2)
	perParticle := sim.Spacing * sim.Spacing * math.Sqrt(3) / 2
	m.scale = math.Sqrt(pw * ph * referenceFill / (float64(m.opts.Particles) * perParticle))
	m.scale = min(max(m.scale, 1.4), 9)

	if m.world == nil {
		m.world = sim.New(pw/m.scale, ph/m.scale, m.opts.Seed)
	} else {
		m.world.Resize(pw/m.scale, ph/m.scale)
	}
	m.world.Populate(scene)
	m.gravityOn = scene.Gravity() != (sim.Vec{})
	if m.gravityOn && m.gravity == (sim.Vec{}) {
		m.gravity = sim.Vec{X: 0, Y: 1}
	}
	m.applyGravity()
	m.world.MaxParticles = m.maxParticles()
	m.debt = 0
	m.stale = true
}

func (m *Model) maxParticles() int {
	return max(m.opts.Particles*5/2, m.world.Len())
}

func (m *Model) applyGravity() {
	if m.world == nil {
		return
	}
	if m.gravityOn {
		m.world.Gravity = m.gravity
	} else {
		m.world.Gravity = sim.Vec{}
	}
}

// advance runs one frame: it updates the brush from the mouse, steps the
// simulation by the time since the last frame, and updates the stats.
func (m *Model) advance() {
	now := m.opts.Now()
	elapsed := min(now.Sub(m.lastTick).Seconds(), 0.1)
	m.lastTick = now

	m.frames++
	if since := now.Sub(m.fpsSince).Seconds(); since >= 0.5 {
		m.fps = float64(m.frames) / since
		m.frames = 0
		m.fpsSince = now
	}
	if m.world == nil {
		return
	}

	m.updateBrush(now, elapsed)
	if !m.paused {
		start := time.Now()
		m.debt += elapsed
		steps := 0
		for m.debt >= sim.StepDuration && steps < maxStepsPerFrame {
			m.world.Step(sim.StepDuration)
			m.debt -= sim.StepDuration
			steps++
		}
		if steps == maxStepsPerFrame {
			m.debt = 0
		}
		ms := float64(time.Since(start).Microseconds()) / 1000
		m.stepMillis += (ms - m.stepMillis) * 0.1
	}
	m.stale = true
}

// updateBrush points the simulation's brush at the cursor and picks its tool.
func (m *Model) updateBrush(now time.Time, elapsed float64) {
	// Motion events stop when the cursor stops, so let the velocity decay
	// between events.
	if now.Sub(m.mouse.at) > 50*time.Millisecond {
		decay := math.Exp(-elapsed / 0.08)
		m.mouse.vel.X *= decay
		m.mouse.vel.Y *= decay
	}
	m.world.Brush = sim.Brush{
		Tool:   m.tool(now),
		Pos:    sim.Vec{X: m.mouse.px / m.scale, Y: m.mouse.py / m.scale},
		Vel:    m.mouse.vel,
		Radius: m.brush,
	}
}

// modifierTimeout is how long a modifier seen on the last mouse event keeps
// its hover tool active. Terminals only report modifiers with mouse events, so
// the model can't tell when a modifier is released while the cursor is still.
const modifierTimeout = 1500 * time.Millisecond

// tool returns the brush tool for the current mouse state. Buttons win over
// modifiers, and modifiers win over the hover tool.
func (m *Model) tool(now time.Time) sim.Tool {
	switch m.mouse.button {
	case tea.MouseLeft:
		return sim.ToolPush
	case tea.MouseRight:
		return sim.ToolPull
	case tea.MouseMiddle:
		return sim.ToolPour
	}
	if !m.mouse.over || m.help {
		return sim.ToolNone
	}
	if now.Sub(m.mouse.at) < modifierTimeout {
		switch {
		case m.mouse.mod&tea.ModCtrl != 0:
			return sim.ToolDisperse
		case m.mouse.mod&(tea.ModShift|tea.ModAlt) != 0:
			return sim.ToolAttract
		}
	}
	return m.hoverTool
}
