// Command liquid simulates a tank of liquid in the terminal.
//
// Drag with the left button to push the liquid away, drag with the right
// button to pull it into a blob, and hold Shift or Ctrl while moving the
// cursor to attract or disperse it. Press ? in the program for every control.
package main

import (
	"flag"
	"fmt"
	"math/rand/v2"
	"os"
	"strings"

	tea "charm.land/bubbletea/v2"

	"github.com/imjasonh/playground/liquid/internal/render"
	"github.com/imjasonh/playground/liquid/internal/sim"
	"github.com/imjasonh/playground/liquid/internal/ui"
)

func main() {
	var sceneNames, modeNames []string
	for _, s := range sim.Scenes {
		sceneNames = append(sceneNames, s.Short())
	}
	for _, m := range render.Modes {
		modeNames = append(modeNames, m.String())
	}
	var themeNames []string
	for _, t := range render.Themes {
		themeNames = append(themeNames, t.Name)
	}

	sceneFlag := flag.String("scene", "dam", "starting scene: "+strings.Join(sceneNames, ", "))
	themeFlag := flag.String("theme", render.Themes[0].Name, "color theme: "+strings.Join(themeNames, ", "))
	viewFlag := flag.String("view", render.ModeLiquid.String(), "how to draw the liquid: "+strings.Join(modeNames, ", "))
	particles := flag.Int("particles", 2200, "about how many particles each scene starts with")
	fps := flag.Int("fps", 60, "frames per second, from 10 to 120")
	seed := flag.Uint64("seed", 0, "seed for the random jitter in scenes; 0 picks one at random")
	flag.Parse()

	opts := ui.Options{
		Particles: min(max(*particles, 100), 20000),
		FPS:       min(max(*fps, 10), 120),
		Seed:      *seed,
	}
	if opts.Seed == 0 {
		opts.Seed = rand.Uint64()
	}

	found := false
	for _, s := range sim.Scenes {
		if s.Short() == *sceneFlag {
			opts.Scene, found = s, true
		}
	}
	if !found {
		fail("unknown scene %q; want one of %s", *sceneFlag, strings.Join(sceneNames, ", "))
	}
	if opts.Theme = render.ThemeNamed(*themeFlag); opts.Theme == nil {
		fail("unknown theme %q; want one of %s", *themeFlag, strings.Join(themeNames, ", "))
	}
	found = false
	for _, m := range render.Modes {
		if m.String() == *viewFlag {
			opts.Mode, found = m, true
		}
	}
	if !found {
		fail("unknown view %q; want one of %s", *viewFlag, strings.Join(modeNames, ", "))
	}

	m := ui.New(opts)
	defer m.Close()
	if _, err := tea.NewProgram(m, tea.WithFPS(opts.FPS)).Run(); err != nil {
		fail("%v", err)
	}
}

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "liquid: "+format+"\n", args...)
	os.Exit(2)
}
