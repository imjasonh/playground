// Command liquid simulates a tank of liquid in the terminal.
//
// Drag with the left button to push the liquid away, drag with the right
// button to pull it into a blob, and hold Shift or Ctrl while moving the
// cursor to attract or disperse it. Press ? in the program for every control.
package main

import (
	"context"
	"fmt"
	"log"
	"math/rand/v2"
	"strings"

	tea "charm.land/bubbletea/v2"
	"github.com/spf13/cobra"

	"github.com/imjasonh/playground/liquid/internal/render"
	"github.com/imjasonh/playground/liquid/internal/sim"
	"github.com/imjasonh/playground/liquid/internal/ui"
	whbiab "github.com/imjasonh/playground/wehadababyitsaboy/go"
)

func main() {
	if err := whbiab.Execute(context.Background(), newRoot()); err != nil {
		log.Fatal("liquid:", err)
	}
}

// options holds the flags of the liquid command.
type options struct {
	scene, theme, view string
	particles, fps     int
	seed               uint64
}

func newRoot() *cobra.Command {
	o := options{
		scene:     "dam",
		theme:     render.Themes[0].Name,
		view:      render.ModeLiquid.String(),
		particles: 2200,
		fps:       60,
	}
	cmd := &cobra.Command{
		Use:           "liquid",
		Short:         "Simulate a tank of liquid in the terminal",
		SilenceUsage:  true,
		SilenceErrors: true,
		RunE: func(*cobra.Command, []string) error {
			return run(o)
		},
	}
	f := cmd.Flags()
	f.StringVar(&o.scene, "scene", o.scene, "starting scene: "+sceneNames())
	f.StringVar(&o.theme, "theme", o.theme, "color theme: "+themeNames())
	f.StringVar(&o.view, "view", o.view, "how to draw the liquid: "+modeNames())
	f.IntVar(&o.particles, "particles", o.particles, "about how many particles each scene starts with")
	f.IntVar(&o.fps, "fps", o.fps, "frames per second, from 10 to 120")
	f.Uint64Var(&o.seed, "seed", o.seed, "seed for the random jitter in scenes; 0 picks one at random")
	return cmd
}

func run(o options) error {
	opts := ui.Options{
		Particles: min(max(o.particles, 100), 20000),
		FPS:       min(max(o.fps, 10), 120),
		Seed:      o.seed,
	}
	if opts.Seed == 0 {
		opts.Seed = rand.Uint64()
	}

	found := false
	for _, s := range sim.Scenes {
		if s.Short() == o.scene {
			opts.Scene, found = s, true
		}
	}
	if !found {
		return fmt.Errorf("unknown scene %q; want one of %s", o.scene, sceneNames())
	}
	if opts.Theme = render.ThemeNamed(o.theme); opts.Theme == nil {
		return fmt.Errorf("unknown theme %q; want one of %s", o.theme, themeNames())
	}
	found = false
	for _, m := range render.Modes {
		if m.String() == o.view {
			opts.Mode, found = m, true
		}
	}
	if !found {
		return fmt.Errorf("unknown view %q; want one of %s", o.view, modeNames())
	}

	m := ui.New(opts)
	defer m.Close()
	_, err := tea.NewProgram(m, tea.WithFPS(opts.FPS)).Run()
	return err
}

func sceneNames() string {
	var names []string
	for _, s := range sim.Scenes {
		names = append(names, s.Short())
	}
	return strings.Join(names, ", ")
}

func themeNames() string {
	var names []string
	for _, t := range render.Themes {
		names = append(names, t.Name)
	}
	return strings.Join(names, ", ")
}

func modeNames() string {
	var names []string
	for _, m := range render.Modes {
		names = append(names, m.String())
	}
	return strings.Join(names, ", ")
}
