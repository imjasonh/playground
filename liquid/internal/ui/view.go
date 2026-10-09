package ui

import (
	"fmt"
	"image/color"
	"strconv"
	"strings"

	"charm.land/lipgloss/v2"

	"github.com/imjasonh/playground/liquid/internal/render"
	"github.com/imjasonh/playground/liquid/internal/sim"
)

// The smallest tank the layout supports, in cells.
const (
	minCols = 54
	minRows = 8
)

var (
	colorText    = lipgloss.Color("#c9cfdb")
	colorDim     = lipgloss.Color("#6c7488")
	colorInk     = lipgloss.Color("#0b0e14")
	colorButton  = lipgloss.Color("#1a1f2b")
	colorHover   = lipgloss.Color("#2b3346")
	colorPanel   = lipgloss.Color("#0f131c")
	colorBorder  = lipgloss.Color("#3a4256")
	colorPaused  = lipgloss.Color("#ffd166")
	toolColorFor = map[sim.Tool]color.Color{
		sim.ToolPush:     lipgloss.Color("#ff7a59"),
		sim.ToolPull:     lipgloss.Color("#6dffb0"),
		sim.ToolAttract:  lipgloss.Color("#7cc8ff"),
		sim.ToolDisperse: lipgloss.Color("#d79bff"),
		sim.ToolPour:     lipgloss.Color("#ffe27a"),
	}
)

type styles struct {
	accent      color.Color
	title       lipgloss.Style
	dim         lipgloss.Style
	stat        lipgloss.Style
	badge       lipgloss.Style
	button      lipgloss.Style
	buttonHover lipgloss.Style
	buttonOn    lipgloss.Style
	panel       lipgloss.Style
	panelKey    lipgloss.Style
	panelText   lipgloss.Style
	panelHead   lipgloss.Style
}

func newStyles(t *render.Theme) styles {
	base := lipgloss.NewStyle()
	button := base.Foreground(colorText).Background(colorButton).Padding(0, 1)
	return styles{
		accent:      t.Accent,
		title:       base.Bold(true).Foreground(colorInk).Background(t.Accent).Padding(0, 1),
		dim:         base.Foreground(colorDim),
		stat:        base.Foreground(colorText),
		badge:       base.Bold(true).Foreground(colorInk).Background(colorPaused).Padding(0, 1),
		button:      button,
		buttonHover: button.Background(colorHover).Foreground(lipgloss.Color("#ffffff")),
		buttonOn:    button.Bold(true).Foreground(colorInk).Background(t.Accent),
		panel: base.Background(colorPanel).
			Border(lipgloss.RoundedBorder()).
			BorderForeground(t.Accent).
			BorderBackground(colorPanel).
			Padding(1, 2),
		panelKey:  base.Bold(true).Foreground(t.Accent).Background(colorPanel),
		panelText: base.Foreground(colorText).Background(colorPanel),
		panelHead: base.Bold(true).Foreground(colorDim).Background(colorPanel),
	}
}

// compose renders the whole screen.
func (m *Model) compose() string {
	if m.world == nil || m.cols < minCols || m.rows < minRows {
		msg := fmt.Sprintf("liquid needs a terminal of at least %d×%d cells", minCols+2, minRows+4)
		return lipgloss.Place(max(m.width, 1), max(m.height, 1), lipgloss.Center, lipgloss.Center, m.st.dim.Render(msg))
	}

	tank := m.rend.Render(render.Frame{
		World: m.world,
		Scale: m.scale,
		Cols:  m.cols,
		Rows:  m.rows,
		Mode:  m.mode,
		Theme: m.currentTheme(),
		Ring:  m.ring(),
	})
	switch {
	case m.help:
		tank = m.overlay(tank, m.helpPanel(), -1)
	case m.opts.Now().Before(m.hintUntil):
		tank = m.overlay(tank, m.hint(), 1)
	}

	border := colorBorder
	if c, ok := toolColorFor[m.world.Brush.Tool]; ok {
		border = c
	}
	box := lipgloss.NewStyle().
		Border(lipgloss.RoundedBorder()).
		BorderForeground(border).
		Render(m.zones.Mark(zoneTank, tank))

	return m.header() + "\n" + box + "\n" + m.toolbar()
}

// overlay draws panel over the tank, centered horizontally. A negative y
// centers it vertically too.
func (m *Model) overlay(tank, panel string, y int) string {
	w, h := lipgloss.Size(panel)
	if w > m.cols || h > m.rows {
		return tank
	}
	x := (m.cols - w) / 2
	if y < 0 {
		y = (m.rows - h) / 2
	}
	y = min(y, m.rows-h)
	return lipgloss.NewCompositor(
		lipgloss.NewLayer(tank),
		lipgloss.NewLayer(panel).X(x).Y(y).Z(1),
	).Render()
}

func (m *Model) ring() render.Ring {
	style := render.RingIdle
	switch m.world.Brush.Tool {
	case sim.ToolPush:
		style = render.RingPush
	case sim.ToolPull:
		style = render.RingPull
	case sim.ToolAttract:
		style = render.RingAttract
	case sim.ToolDisperse:
		style = render.RingDisperse
	case sim.ToolPour:
		style = render.RingPour
	}
	return render.Ring{
		Visible: !m.help && (m.mouse.over || m.mouse.button != 0),
		X:       m.mouse.px,
		Y:       m.mouse.py,
		Radius:  m.brush * m.scale,
		Style:   style,
	}
}

func (m *Model) header() string {
	left := m.st.title.Render("≋ liquid") + "  " + m.st.stat.Render(m.scene.String())
	if m.paused {
		left += "  " + m.st.badge.Render("paused")
	}

	var stats []string
	if tool := m.world.Brush.Tool; tool != sim.ToolNone {
		stats = append(stats, lipgloss.NewStyle().Bold(true).Foreground(toolColorFor[tool]).Render("● "+tool.String()))
	}
	stats = append(stats,
		m.st.stat.Render(gravityArrow(m.gravityOn, m.gravity))+m.st.dim.Render(" gravity"),
		m.st.stat.Render(commas(m.world.Len()))+m.st.dim.Render(" particles"),
		m.st.stat.Render(strconv.Itoa(int(m.fps+0.5)))+m.st.dim.Render(" fps"),
		m.st.stat.Render(fmt.Sprintf("%.1f", m.stepMillis))+m.st.dim.Render(" ms"),
	)
	// Drop stats from the front until the header fits, keeping fps and timing.
	for len(stats) > 0 {
		right := strings.Join(stats, "   ")
		if gap := m.width - lipgloss.Width(left) - lipgloss.Width(right) - 1; gap >= 1 {
			return left + strings.Repeat(" ", gap) + right + " "
		}
		stats = stats[1:]
	}
	return left
}

// button is a toolbar button. labels holds its label from longest to
// shortest; the toolbar uses the longest set of labels that fits.
type button struct {
	id     string
	labels [3]string
	on     bool
	style  *lipgloss.Style
}

func (m *Model) buttons() []button {
	pause := button{id: zonePause, labels: [3]string{"‖ pause", "‖", "‖"}}
	if m.paused {
		pause = button{id: zonePause, labels: [3]string{"▸ play", "▸", "▸"}, on: true}
	}
	bs := []button{pause, {id: zoneReset, labels: [3]string{"↺ reset", "↺", "↺"}}}
	for i, s := range sim.Scenes {
		n := strconv.Itoa(i + 1)
		label := n + " " + s.Short()
		bs = append(bs, button{id: zoneForScene(s), labels: [3]string{label, label, n}, on: s == m.scene})
	}
	themeStyle := m.st.button.Foreground(m.st.accent)
	hover := "off"
	if m.hoverTool != sim.ToolNone {
		hover = m.hoverTool.String()
	}
	arrow := gravityArrow(m.gravityOn, m.gravity)
	mode := "◐ " + m.mode.String()
	theme := "◆ " + m.currentTheme().Name
	return append(bs,
		button{id: zoneMode, labels: [3]string{mode, mode, "◐"}},
		button{id: zoneTheme, labels: [3]string{theme, theme, "◆"}, style: &themeStyle},
		button{id: zoneGravity, labels: [3]string{arrow + " gravity", arrow, arrow}, on: !m.gravityOn},
		button{id: zoneHover, labels: [3]string{"◎ hover " + hover, "◎ " + hover, "◎"}, on: m.hoverTool != sim.ToolNone},
		button{id: zoneHelp, labels: [3]string{"? help", "?", "?"}, on: m.help},
		button{id: zoneQuit, labels: [3]string{"✕ quit", "✕", "✕"}},
	)
}

// toolbar renders the buttons, each marked as a zone.
func (m *Model) toolbar() string {
	bs := m.buttons()
	draw := func(tier int) string {
		parts := make([]string, 0, len(bs))
		for _, b := range bs {
			style := m.st.button
			switch {
			case b.on:
				style = m.st.buttonOn
			case b.id == m.hoverZone:
				style = m.st.buttonHover
			case b.style != nil:
				style = *b.style
			}
			parts = append(parts, m.zones.Mark(b.id, style.Render(b.labels[tier])))
		}
		return " " + strings.Join(parts, " ")
	}
	for tier := range 2 {
		if bar := draw(tier); lipgloss.Width(bar) <= m.width {
			return bar
		}
	}
	return draw(2)
}

// hint is the one-line reminder of the mouse controls shown at startup.
func (m *Model) hint() string {
	type item struct{ key, text string }
	items := []item{
		{"drag", "push"},
		{"right-drag", "pull"},
		{"shift+move", "attract"},
		{"ctrl+move", "disperse"},
		{"?", "help"},
	}
	for len(items) > 0 {
		var b strings.Builder
		b.WriteString(m.st.panelText.Render(" "))
		for i, it := range items {
			if i > 0 {
				b.WriteString(m.st.panelHead.Render(" · "))
			}
			b.WriteString(m.st.panelKey.Render(it.key) + m.st.panelText.Render(" "+it.text))
		}
		b.WriteString(m.st.panelText.Render(" "))
		if s := b.String(); lipgloss.Width(s) <= m.cols-4 {
			return s
		}
		items = items[:len(items)-1]
	}
	return ""
}

// helpPanel lists every control.
func (m *Model) helpPanel() string {
	type row struct{ key, text string }
	columns := []struct {
		title string
		rows  []row
	}{
		{"mouse", []row{
			{"drag", "push"},
			{"right drag", "pull"},
			{"middle drag", "pour"},
			{"shift+move", "attract"},
			{"ctrl+move", "disperse"},
			{"wheel", "brush size"},
		}},
		{"liquid", []row{
			{"space", "pause"},
			{".", "step"},
			{"r", "reset"},
			{"1-5", "scenes"},
			{"s", "shake"},
			{"tab", "hover tool"},
		}},
		{"tank", []row{
			{"arrows", "tilt gravity"},
			{"g", "zero-g"},
			{"v", "view"},
			{"c", "colors"},
			{"[ ]", "brush size"},
			{"q", "quit"},
		}},
	}

	var blocks []string
	for _, col := range columns {
		keyWidth := 0
		for _, r := range col.rows {
			keyWidth = max(keyWidth, lipgloss.Width(r.key))
		}
		lines := []string{m.st.panelHead.Render(col.title)}
		for _, r := range col.rows {
			pad := strings.Repeat(" ", keyWidth-lipgloss.Width(r.key)+2)
			lines = append(lines, m.st.panelKey.Render(r.key)+m.st.panelText.Render(pad+r.text))
		}
		blocks = append(blocks, block(lines, m.st.panelText))
	}

	gap := m.st.panelText.Render("    ")
	body := blocks[0]
	for _, b := range blocks[1:] {
		body = joinBlocks(body, gap, b, m.st.panelText)
	}
	title := m.st.panelKey.Render("≋ liquid") + m.st.panelText.Render("  controls")
	content := block([]string{title, "", body}, m.st.panelText)
	return m.st.panel.Render(content)
}

// block pads lines to the same width with spaces in style, so a panel with a
// background has no holes.
func block(lines []string, style lipgloss.Style) string {
	var all []string
	for _, l := range lines {
		all = append(all, strings.Split(l, "\n")...)
	}
	width := 0
	for _, l := range all {
		width = max(width, lipgloss.Width(l))
	}
	for i, l := range all {
		if pad := width - lipgloss.Width(l); pad > 0 {
			all[i] = l + style.Render(strings.Repeat(" ", pad))
		}
	}
	return strings.Join(all, "\n")
}

// joinBlocks places blocks side by side with a gap, padding the shorter one
// with spaces in style.
func joinBlocks(a, gap, b string, style lipgloss.Style) string {
	al, bl := strings.Split(a, "\n"), strings.Split(b, "\n")
	aw, bw := lipgloss.Width(a), lipgloss.Width(b)
	n := max(len(al), len(bl))
	lines := make([]string, n)
	for i := range n {
		l := style.Render(strings.Repeat(" ", aw))
		if i < len(al) {
			l = al[i]
		}
		r := style.Render(strings.Repeat(" ", bw))
		if i < len(bl) {
			r = bl[i]
		}
		lines[i] = l + gap + r
	}
	return strings.Join(lines, "\n")
}

func gravityArrow(on bool, g sim.Vec) string {
	switch {
	case !on:
		return "○"
	case g.Y < 0:
		return "↑"
	case g.X < 0:
		return "←"
	case g.X > 0:
		return "→"
	default:
		return "↓"
	}
}

// commas formats n with thousands separators.
func commas(n int) string {
	s := strconv.Itoa(n)
	for i := len(s) - 3; i > 0; i -= 3 {
		s = s[:i] + "," + s[i:]
	}
	return s
}
