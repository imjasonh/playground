package ui

import (
	"math"
	"math/rand/v2"
	"strconv"
	"strings"
	"time"

	tea "charm.land/bubbletea/v2"

	"github.com/imjasonh/playground/liquid/internal/render"
	"github.com/imjasonh/playground/liquid/internal/sim"
)

// Zone IDs. The tank is one zone, and every toolbar button is another.
const (
	zoneTank    = "tank"
	zonePause   = "pause"
	zoneReset   = "reset"
	zoneMode    = "mode"
	zoneTheme   = "theme"
	zoneGravity = "gravity"
	zoneHover   = "hover"
	zoneHelp    = "help"
	zoneQuit    = "quit"
	sceneZone   = "scene-"
)

func zoneForScene(s sim.Scene) string { return sceneZone + strconv.Itoa(int(s)) }

// buttonZones lists every button zone, for hit testing.
var buttonZones = func() []string {
	ids := []string{zonePause, zoneReset}
	for _, s := range sim.Scenes {
		ids = append(ids, zoneForScene(s))
	}
	return append(ids, zoneMode, zoneTheme, zoneGravity, zoneHover, zoneHelp, zoneQuit)
}()

// buttonAt returns the ID of the button under the mouse, or "".
func (m *Model) buttonAt(msg tea.MouseMsg) string {
	for _, id := range buttonZones {
		if m.zones.Get(id).InBounds(msg) {
			return id
		}
	}
	return ""
}

// maxCursorSpeed caps the cursor velocity that the brush passes on to the
// liquid, in h/s.
const maxCursorSpeed = 60.0

// trackMouse records the cursor position and modifiers from a mouse event,
// using the tank zone to convert the terminal cell into a pixel in the tank.
func (m *Model) trackMouse(msg tea.MouseMsg) {
	now := m.opts.Now()
	ev := msg.Mouse()
	prevAt := m.mouse.at
	wasOver := m.mouse.over || m.mouse.button != tea.MouseNone
	m.mouse.mod = ev.Mod
	m.mouse.at = now

	z := m.zones.Get(zoneTank)
	if z.IsZero() || m.world == nil {
		m.mouse.over = false
		return
	}
	m.mouse.over = z.InBounds(msg)
	if !m.mouse.over && m.mouse.button == tea.MouseNone {
		return
	}

	// Aim at the center of the cell. During a drag that leaves the tank, keep
	// acting at the nearest edge.
	cx := min(max(ev.X-z.StartX, 0), m.cols-1)
	cy := min(max(ev.Y-z.StartY, 0), m.rows-1)
	px, py := float64(cx)+0.5, float64(cy)*2+1

	if dt := now.Sub(prevAt).Seconds(); wasOver && dt > 0 && dt < 0.25 {
		vx := (px - m.mouse.px) / m.scale / dt
		vy := (py - m.mouse.py) / m.scale / dt
		a := 1 - math.Exp(-dt/0.05)
		m.mouse.vel.X += (vx - m.mouse.vel.X) * a
		m.mouse.vel.Y += (vy - m.mouse.vel.Y) * a
		if s := math.Hypot(m.mouse.vel.X, m.mouse.vel.Y); s > maxCursorSpeed {
			m.mouse.vel.X *= maxCursorSpeed / s
			m.mouse.vel.Y *= maxCursorSpeed / s
		}
	} else if !wasOver {
		m.mouse.vel = sim.Vec{}
	}
	m.mouse.px, m.mouse.py = px, py
}

func (m *Model) onMouseDown(msg tea.MouseClickMsg) {
	m.stale = true
	if m.help {
		m.help = false
		return
	}
	if id := m.buttonAt(msg); id != "" {
		m.pressedZone = id
		return
	}
	m.trackMouse(msg)
	if !m.mouse.over {
		return
	}
	switch msg.Button {
	case tea.MouseLeft, tea.MouseRight, tea.MouseMiddle:
		m.mouse.button = msg.Button
		m.hintUntil = time.Time{}
	}
}

func (m *Model) onMouseUp(msg tea.MouseReleaseMsg) tea.Cmd {
	m.stale = true
	if id := m.pressedZone; id != "" {
		m.pressedZone = ""
		if m.buttonAt(msg) == id {
			return m.press(id)
		}
		return nil
	}
	m.trackMouse(msg)
	m.mouse.button = tea.MouseNone
	return nil
}

func (m *Model) onMouseMove(msg tea.MouseMotionMsg) {
	if id := m.buttonAt(msg); id != m.hoverZone {
		m.hoverZone = id
		m.stale = true
	}
	// Motion without a button means no button is down, even if the release
	// happened outside the window and never arrived.
	if msg.Button == tea.MouseNone {
		m.mouse.button = tea.MouseNone
	}
	m.trackMouse(msg)
}

func (m *Model) onWheel(msg tea.MouseWheelMsg) {
	switch msg.Button {
	case tea.MouseWheelUp:
		m.resizeBrush(1.15)
	case tea.MouseWheelDown:
		m.resizeBrush(1 / 1.15)
	}
	m.trackMouse(msg)
}

func (m *Model) resizeBrush(factor float64) {
	m.brush = min(max(m.brush*factor, minBrush), maxBrush)
	m.stale = true
}

// press activates a toolbar button.
func (m *Model) press(id string) tea.Cmd {
	m.stale = true
	switch id {
	case zonePause:
		m.paused = !m.paused
	case zoneReset:
		m.reset(m.scene)
	case zoneMode:
		m.cycleMode()
	case zoneTheme:
		m.cycleTheme()
	case zoneGravity:
		m.gravityOn = !m.gravityOn
		m.applyGravity()
	case zoneHover:
		m.cycleHover()
	case zoneHelp:
		m.help = !m.help
	case zoneQuit:
		return tea.Quit
	default:
		if n, err := strconv.Atoi(strings.TrimPrefix(id, sceneZone)); err == nil && n >= 0 && n < len(sim.Scenes) {
			m.reset(sim.Scenes[n])
		}
	}
	return nil
}

func (m *Model) onKey(msg tea.KeyPressMsg) tea.Cmd {
	m.stale = true
	key := msg.String()
	if m.help {
		switch key {
		case "ctrl+c", "q":
			return tea.Quit
		case "esc", "?", "h", "enter", "space":
			m.help = false
			return nil
		}
	}
	switch key {
	case "ctrl+c", "q":
		return tea.Quit
	case "?", "h":
		m.help = true
	case "space", "p":
		m.paused = !m.paused
	case ".":
		if m.paused && m.world != nil {
			for range 3 {
				m.world.Step(sim.StepDuration)
			}
		}
	case "r":
		if m.world != nil {
			m.reset(m.scene)
		}
	case "1", "2", "3", "4", "5":
		if m.world != nil {
			m.reset(sim.Scenes[key[0]-'1'])
		}
	case "v", "m":
		m.cycleMode()
	case "c", "t":
		m.cycleTheme()
	case "up":
		m.setGravity(sim.Vec{X: 0, Y: -1})
	case "down":
		m.setGravity(sim.Vec{X: 0, Y: 1})
	case "left":
		m.setGravity(sim.Vec{X: -1, Y: 0})
	case "right":
		m.setGravity(sim.Vec{X: 1, Y: 0})
	case "g":
		m.gravityOn = !m.gravityOn
		m.applyGravity()
	case "s":
		m.shake()
	case "tab":
		m.cycleHover()
	case "[", "-":
		m.resizeBrush(1 / 1.15)
	case "]", "+", "=":
		m.resizeBrush(1.15)
	}
	return nil
}

func (m *Model) cycleMode() {
	m.mode = render.Modes[(int(m.mode)+1)%len(render.Modes)]
}

func (m *Model) cycleTheme() {
	m.theme = (m.theme + 1) % len(render.Themes)
	m.st = newStyles(m.currentTheme())
}

func (m *Model) cycleHover() {
	switch m.hoverTool {
	case sim.ToolNone:
		m.hoverTool = sim.ToolAttract
	case sim.ToolAttract:
		m.hoverTool = sim.ToolDisperse
	default:
		m.hoverTool = sim.ToolNone
	}
}

func (m *Model) setGravity(dir sim.Vec) {
	m.gravity = dir
	m.gravityOn = true
	m.applyGravity()
}

// shake kicks the liquid sideways and against gravity, as if someone bumped
// the tank.
func (m *Model) shake() {
	if m.world == nil {
		return
	}
	g := m.gravity
	if !m.gravityOn {
		g = sim.Vec{X: 0, Y: 1}
	}
	side := 1.0
	if rand.IntN(2) == 0 {
		side = -1
	}
	dir := sim.Vec{X: -g.Y*side - g.X*0.6, Y: g.X*side - g.Y*0.6}
	n := math.Hypot(dir.X, dir.Y)
	m.world.Shake(sim.Vec{X: dir.X / n, Y: dir.Y / n}, 16)
}
