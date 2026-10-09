package ui

import (
	"math"
	"strings"
	"testing"
	"time"

	tea "charm.land/bubbletea/v2"
	"github.com/charmbracelet/x/ansi"

	"github.com/imjasonh/playground/liquid/internal/render"
	"github.com/imjasonh/playground/liquid/internal/sim"
)

type clock struct{ t time.Time }

func (c *clock) now() time.Time { return c.t }

func newModel(t *testing.T, width, height int, scene sim.Scene) (*Model, *clock) {
	t.Helper()
	c := &clock{t: time.Unix(1_700_000_000, 0)}
	m := New(Options{Scene: scene, Particles: 900, Seed: 1, Now: c.now})
	t.Cleanup(m.Close)
	m.Update(tea.WindowSizeMsg{Width: width, Height: height})
	view(t, m)
	return m, c
}

// view renders the model and waits until the zone manager has recorded the
// tank zone.
func view(t *testing.T, m *Model) string {
	t.Helper()
	content := m.View().Content
	waitFor(t, "tank zone", func() bool { return !m.zones.Get(zoneTank).IsZero() })
	return content
}

func waitFor(t *testing.T, what string, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(time.Millisecond)
	}
}

// buttonCell returns a cell inside the toolbar button with the given label,
// after waiting for the zone manager to place that button's zone there.
func buttonCell(t *testing.T, m *Model, id, label string) (x, y int) {
	t.Helper()
	lines := strings.Split(ansi.Strip(view(t, m)), "\n")
	y = len(lines) - 1
	i := strings.Index(lines[y], label)
	if i < 0 {
		t.Fatalf("toolbar %q has no %q button", lines[y], label)
	}
	x = ansi.StringWidth(lines[y][:i])
	msg := tea.MouseClickMsg{X: x, Y: y}
	waitFor(t, "zone "+id, func() bool { return m.zones.Get(id).InBounds(msg) })
	return x, y
}

func click(t *testing.T, m *Model, id, label string) tea.Cmd {
	t.Helper()
	x, y := buttonCell(t, m, id, label)
	m.Update(tea.MouseClickMsg{X: x, Y: y, Button: tea.MouseLeft})
	_, cmd := m.Update(tea.MouseReleaseMsg{X: x, Y: y, Button: tea.MouseLeft})
	return cmd
}

// tick advances the clock by one frame and delivers a tick.
func tick(m *Model, c *clock) {
	c.t = c.t.Add(time.Second / 60)
	m.Update(tickMsg(c.t))
}

// The tank starts below the one-line header and inside a one-cell border.
const tankX, tankY = 1, 2

func isQuit(cmd tea.Cmd) bool {
	if cmd == nil {
		return false
	}
	_, ok := cmd().(tea.QuitMsg)
	return ok
}

func TestLayoutFitsTerminal(t *testing.T) {
	for _, size := range [][2]int{{60, 16}, {100, 30}, {120, 36}, {220, 60}} {
		m, _ := newModel(t, size[0], size[1], sim.SceneDam)
		lines := strings.Split(view(t, m), "\n")
		if len(lines) != size[1] {
			t.Errorf("%dx%d: view has %d lines, want %d", size[0], size[1], len(lines), size[1])
		}
		for i, l := range lines {
			if w := ansi.StringWidth(l); w > size[0] {
				t.Errorf("%dx%d: line %d is %d cells wide", size[0], size[1], i, w)
			}
		}
		if !strings.Contains(ansi.Strip(lines[0]), "liquid") {
			t.Errorf("%dx%d: header %q doesn't name the program", size[0], size[1], ansi.Strip(lines[0]))
		}
		if !strings.Contains(ansi.Strip(lines[len(lines)-1]), "?") {
			t.Errorf("%dx%d: toolbar %q has no help button", size[0], size[1], ansi.Strip(lines[len(lines)-1]))
		}
	}
}

func TestTooSmallTerminal(t *testing.T) {
	c := &clock{t: time.Unix(1_700_000_000, 0)}
	m := New(Options{Now: c.now})
	t.Cleanup(m.Close)
	m.Update(tea.WindowSizeMsg{Width: 30, Height: 10})
	if got := ansi.Strip(m.View().Content); !strings.Contains(got, "needs a terminal") {
		t.Errorf("view of a 30x10 terminal is %q, want a message asking for a bigger one", got)
	}
}

func TestDragPushesAtCursor(t *testing.T) {
	m, c := newModel(t, 100, 30, sim.ScenePool)
	m.Update(tea.MouseClickMsg{X: tankX + 40, Y: tankY + 10, Button: tea.MouseLeft})
	tick(m, c)
	b := m.world.Brush
	if b.Tool != sim.ToolPush {
		t.Fatalf("brush tool while dragging is %v, want push", b.Tool)
	}
	wantX, wantY := 40.5/m.scale, 21/m.scale
	if math.Abs(b.Pos.X-wantX) > 1e-9 || math.Abs(b.Pos.Y-wantY) > 1e-9 {
		t.Errorf("brush at (%.2f, %.2f), want (%.2f, %.2f)", b.Pos.X, b.Pos.Y, wantX, wantY)
	}

	c.t = c.t.Add(10 * time.Millisecond)
	m.Update(tea.MouseMotionMsg{X: tankX + 44, Y: tankY + 10, Button: tea.MouseLeft})
	tick(m, c)
	if got := m.world.Brush.Pos.X; math.Abs(got-44.5/m.scale) > 1e-9 {
		t.Errorf("after dragging right, brush x is %.2f, want %.2f", got, 44.5/m.scale)
	}
	if v := m.world.Brush.Vel.X; v <= 0 {
		t.Errorf("after dragging right, brush velocity is %.2f, want it positive", v)
	}
	if !strings.Contains(ansi.Strip(view(t, m)), "● push") {
		t.Error("header doesn't show the push tool while dragging")
	}

	m.Update(tea.MouseReleaseMsg{X: tankX + 44, Y: tankY + 10, Button: tea.MouseLeft})
	tick(m, c)
	if tool := m.world.Brush.Tool; tool != sim.ToolNone {
		t.Errorf("brush tool after release is %v, want none", tool)
	}
}

func TestDragLeavingTankStaysAtEdge(t *testing.T) {
	m, c := newModel(t, 100, 30, sim.ScenePool)
	m.Update(tea.MouseClickMsg{X: tankX + 10, Y: tankY + 10, Button: tea.MouseRight})
	m.Update(tea.MouseMotionMsg{X: 0, Y: 0, Button: tea.MouseRight})
	tick(m, c)
	b := m.world.Brush
	if b.Tool != sim.ToolPull {
		t.Fatalf("brush tool is %v, want pull", b.Tool)
	}
	if b.Pos.X != 0.5/m.scale || b.Pos.Y != 1/m.scale {
		t.Errorf("brush at (%.2f, %.2f), want the tank's top-left cell", b.Pos.X, b.Pos.Y)
	}
}

func TestMouseButtonsPickTools(t *testing.T) {
	for _, tc := range []struct {
		button tea.MouseButton
		want   sim.Tool
	}{
		{tea.MouseLeft, sim.ToolPush},
		{tea.MouseRight, sim.ToolPull},
		{tea.MouseMiddle, sim.ToolPour},
	} {
		m, c := newModel(t, 100, 30, sim.ScenePool)
		m.Update(tea.MouseClickMsg{X: tankX + 20, Y: tankY + 3, Button: tc.button})
		tick(m, c)
		if got := m.world.Brush.Tool; got != tc.want {
			t.Errorf("%v: brush tool is %v, want %v", tc.button, got, tc.want)
		}
	}
}

func TestPourAddsParticles(t *testing.T) {
	m, c := newModel(t, 100, 30, sim.ScenePool)
	n := m.world.Len()
	m.Update(tea.MouseClickMsg{X: tankX + 20, Y: tankY + 3, Button: tea.MouseMiddle})
	for range 10 {
		tick(m, c)
	}
	if m.world.Len() <= n {
		t.Errorf("after pouring, the tank has %d particles, want more than %d", m.world.Len(), n)
	}
}

func TestModifiersWhileMovingAttractOrDisperse(t *testing.T) {
	for _, tc := range []struct {
		mod  tea.KeyMod
		want sim.Tool
	}{
		{0, sim.ToolNone},
		{tea.ModShift, sim.ToolAttract},
		{tea.ModAlt, sim.ToolAttract},
		{tea.ModCtrl, sim.ToolDisperse},
	} {
		m, c := newModel(t, 100, 30, sim.ScenePool)
		m.Update(tea.MouseMotionMsg{X: tankX + 30, Y: tankY + 8, Mod: tc.mod})
		tick(m, c)
		if got := m.world.Brush.Tool; got != tc.want {
			t.Errorf("moving with modifiers %v: tool is %v, want %v", tc.mod, got, tc.want)
		}

		// With no more mouse events, the model can't tell whether the
		// modifier is still held, so the tool times out.
		c.t = c.t.Add(modifierTimeout)
		tick(m, c)
		if got := m.world.Brush.Tool; got != sim.ToolNone {
			t.Errorf("moving with modifiers %v, then waiting: tool is %v, want none", tc.mod, got)
		}
	}
}

func TestHoverTool(t *testing.T) {
	m, c := newModel(t, 100, 30, sim.ScenePool)
	m.Update(tea.KeyPressMsg{Code: tea.KeyTab})
	m.Update(tea.MouseMotionMsg{X: tankX + 30, Y: tankY + 8})
	tick(m, c)
	if got := m.world.Brush.Tool; got != sim.ToolAttract {
		t.Errorf("after one tab, hovering uses %v, want attract", got)
	}
	m.Update(tea.KeyPressMsg{Code: tea.KeyTab})
	tick(m, c)
	if got := m.world.Brush.Tool; got != sim.ToolDisperse {
		t.Errorf("after two tabs, hovering uses %v, want disperse", got)
	}
	// Hovering over the toolbar leaves the liquid alone.
	m.Update(tea.MouseMotionMsg{X: 5, Y: 29})
	tick(m, c)
	if got := m.world.Brush.Tool; got != sim.ToolNone {
		t.Errorf("outside the tank, the brush uses %v, want none", got)
	}
	m.Update(tea.KeyPressMsg{Code: tea.KeyTab})
	if m.hoverTool != sim.ToolNone {
		t.Errorf("after three tabs, the hover tool is %v, want none", m.hoverTool)
	}
}

func TestToolbarButtons(t *testing.T) {
	m, _ := newModel(t, 160, 40, sim.SceneDam)

	click(t, m, zonePause, "pause")
	if !m.paused {
		t.Error("clicking pause didn't pause")
	}
	click(t, m, zonePause, "play")
	if m.paused {
		t.Error("clicking play didn't resume")
	}

	click(t, m, zoneForScene(sim.SceneDrop), "3 drop")
	if m.scene != sim.SceneDrop {
		t.Errorf("after clicking 3 drop, the scene is %v", m.scene)
	}

	click(t, m, zoneMode, render.ModeLiquid.String())
	if m.mode != render.ModeParticles {
		t.Errorf("after clicking the view button, the view is %v, want particles", m.mode)
	}

	click(t, m, zoneTheme, render.Themes[0].Name)
	if m.currentTheme() != render.Themes[1] {
		t.Errorf("after clicking the theme button, the theme is %v", m.currentTheme().Name)
	}

	click(t, m, zoneGravity, "gravity")
	if m.gravityOn || m.world.Gravity != (sim.Vec{}) {
		t.Errorf("after clicking gravity, gravity is %v", m.world.Gravity)
	}

	click(t, m, zoneHover, "hover off")
	if m.hoverTool != sim.ToolAttract {
		t.Errorf("after clicking hover, the hover tool is %v, want attract", m.hoverTool)
	}

	click(t, m, zoneHelp, "help")
	if !m.help {
		t.Error("clicking help didn't open help")
	}
	if !strings.Contains(ansi.Strip(view(t, m)), "controls") {
		t.Error("help panel isn't drawn")
	}
	m.Update(tea.MouseClickMsg{X: tankX + 3, Y: tankY + 3, Button: tea.MouseLeft})
	if m.help {
		t.Error("clicking the tank didn't close help")
	}
	m.Update(tea.MouseReleaseMsg{X: tankX + 3, Y: tankY + 3, Button: tea.MouseLeft})

	if cmd := click(t, m, zoneQuit, "quit"); !isQuit(cmd) {
		t.Error("clicking quit didn't quit")
	}
}

func TestButtonNeedsPressAndReleaseOnIt(t *testing.T) {
	m, _ := newModel(t, 160, 40, sim.SceneDam)
	px, py := buttonCell(t, m, zonePause, "pause")
	rx, ry := buttonCell(t, m, zoneReset, "reset")
	m.Update(tea.MouseClickMsg{X: px, Y: py, Button: tea.MouseLeft})
	m.Update(tea.MouseReleaseMsg{X: rx, Y: ry, Button: tea.MouseLeft})
	if m.paused {
		t.Error("pressing pause and releasing on reset paused the simulation")
	}
}

func TestKeys(t *testing.T) {
	m, c := newModel(t, 100, 30, sim.SceneDam)
	key := func(s string) tea.Cmd {
		var msg tea.KeyPressMsg
		switch s {
		case "space":
			msg = tea.KeyPressMsg{Code: tea.KeySpace, Text: " "}
		case "right":
			msg = tea.KeyPressMsg{Code: tea.KeyRight}
		case "esc":
			msg = tea.KeyPressMsg{Code: tea.KeyEscape}
		default:
			msg = tea.KeyPressMsg{Code: rune(s[0]), Text: s}
		}
		_, cmd := m.Update(msg)
		return cmd
	}

	key("space")
	if !m.paused {
		t.Error("space didn't pause")
	}
	before := append([]float64(nil), m.world.Y...)
	tick(m, c)
	for i, y := range m.world.Y {
		if y != before[i] {
			t.Fatal("the simulation moved while paused")
		}
	}
	key(".")
	moved := false
	for i, y := range m.world.Y {
		moved = moved || y != before[i]
	}
	if !moved {
		t.Error(". didn't step the paused simulation")
	}
	key("space")

	key("right")
	if m.world.Gravity != (sim.Vec{X: 1, Y: 0}) {
		t.Errorf("after the right arrow, gravity is %v", m.world.Gravity)
	}
	key("g")
	if m.world.Gravity != (sim.Vec{}) {
		t.Errorf("after g, gravity is %v, want none", m.world.Gravity)
	}
	key("2")
	if m.scene != sim.SceneDouble {
		t.Errorf("after 2, the scene is %v", m.scene)
	}
	if m.world.Gravity == (sim.Vec{}) {
		t.Error("choosing a scene with gravity left gravity off")
	}
	key("5")
	if m.world.Gravity != (sim.Vec{}) {
		t.Errorf("the zero-g scene has gravity %v", m.world.Gravity)
	}
	key("v")
	if m.mode != render.ModeParticles {
		t.Errorf("after v, the view is %v", m.mode)
	}
	key("c")
	if m.theme != 1 {
		t.Errorf("after c, the theme is %d", m.theme)
	}

	brush := m.brush
	key("]")
	if m.brush <= brush {
		t.Errorf("] changed the brush from %.2f to %.2f, want bigger", brush, m.brush)
	}
	key("[")
	key("[")
	if m.brush >= brush {
		t.Errorf("[ changed the brush to %.2f, want smaller than %.2f", m.brush, brush)
	}

	key("?")
	if !m.help {
		t.Error("? didn't open help")
	}
	key("esc")
	if m.help {
		t.Error("esc didn't close help")
	}
	if !isQuit(key("q")) {
		t.Error("q didn't quit")
	}
}

func TestWheelResizesBrush(t *testing.T) {
	m, _ := newModel(t, 100, 30, sim.ScenePool)
	start := m.brush
	m.Update(tea.MouseWheelMsg{X: tankX + 10, Y: tankY + 10, Button: tea.MouseWheelUp})
	if m.brush <= start {
		t.Errorf("wheel up changed the brush from %.2f to %.2f, want bigger", start, m.brush)
	}
	for range 50 {
		m.Update(tea.MouseWheelMsg{X: tankX + 10, Y: tankY + 10, Button: tea.MouseWheelDown})
	}
	if m.brush != minBrush {
		t.Errorf("after scrolling down, the brush is %.2f, want the minimum %.2f", m.brush, minBrush)
	}
}

func TestTicksAdvanceSimulation(t *testing.T) {
	m, c := newModel(t, 100, 30, sim.SceneDam)
	before := append([]float64(nil), m.world.X...)
	for range 30 {
		tick(m, c)
	}
	var moved float64
	for i, x := range m.world.X {
		moved = math.Max(moved, math.Abs(x-before[i]))
	}
	if moved < 1 {
		t.Errorf("after half a second, the farthest particle moved %.2f h, want the dam to break", moved)
	}
	if !strings.Contains(ansi.Strip(view(t, m)), "fps") {
		t.Error("header doesn't show the frame rate")
	}
}

func TestResizeKeepsLiquid(t *testing.T) {
	m, _ := newModel(t, 120, 36, sim.ScenePool)
	n := m.world.Len()
	m.Update(tea.WindowSizeMsg{Width: 80, Height: 24})
	if m.world.Len() != n {
		t.Errorf("resizing changed the particle count from %d to %d", n, m.world.Len())
	}
	if want := float64(78) / m.scale; math.Abs(m.world.Width-want) > 1e-9 {
		t.Errorf("tank width is %.2f h, want %.2f", m.world.Width, want)
	}
	for i := range m.world.X {
		if m.world.X[i] > m.world.Width || m.world.Y[i] > m.world.Height {
			t.Fatalf("particle %d at (%.2f, %.2f) is outside the resized tank", i, m.world.X[i], m.world.Y[i])
		}
	}
	lines := strings.Split(view(t, m), "\n")
	if len(lines) != 24 {
		t.Errorf("after resizing, the view has %d lines, want 24", len(lines))
	}
}

func TestHintDisappears(t *testing.T) {
	m, c := newModel(t, 120, 36, sim.SceneDam)
	if !strings.Contains(ansi.Strip(view(t, m)), "right-drag") {
		t.Error("no control hint at startup")
	}
	c.t = c.t.Add(10 * time.Second)
	tick(m, c)
	if strings.Contains(ansi.Strip(view(t, m)), "right-drag") {
		t.Error("control hint still showing after 10 seconds")
	}
}
