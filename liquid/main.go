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

func newRoot() *cobra.Command {
	var sceneNames, modeNames, themeNames []string
	for _, s := range sim.Scenes {
		sceneNames = append(sceneNames, s.Short())
	}
	for _, m := range render.Modes {
		modeNames = append(modeNames, m.String())
	}
	for _, t := range render.Themes {
		themeNames = append(themeNames, t.Name)
	}

	var (
		sceneFlag = "dam"
		themeFlag = render.Themes[0].Name
		viewFlag  = render.ModeLiquid.String()
		particles = 2200
		fps       = 60
		seed      uint64
	)
	cmd := &cobra.Command{
		Use:           "liquid",
		Short:         "Simulate a tank of liquid in the terminal",
		SilenceUsage:  true,
		SilenceErrors: true,
		RunE: func(*cobra.Command, []string) error {
			return run(sceneFlag, themeFlag, viewFlag, particles, fps, seed, sceneNames, modeNames, themeNames)
		},
	}
	f := cmd.Flags()
	f.StringVar(&sceneFlag, "scene", sceneFlag, "starting scene: "+strings.Join(sceneNames, ", "))
	f.StringVar(&themeFlag, "theme", themeFlag, "color theme: "+strings.Join(themeNames, ", "))
	f.StringVar(&viewFlag, "view", viewFlag, "how to draw the liquid: "+strings.Join(modeNames, ", "))
	f.IntVar(&particles, "particles", particles, "about how many particles each scene starts with")
	f.IntVar(&fps, "fps", fps, "frames per second, from 10 to 120")
	f.Uint64Var(&seed, "seed", seed, "seed for the random jitter in scenes; 0 picks one at random")
	return cmd
}

func run(sceneFlag, themeFlag, viewFlag string, particles, fps int, seed uint64, sceneNames, modeNames, themeNames []string) error {
	opts := ui.Options{
		Particles: min(max(particles, 100), 20000),
		FPS:       min(max(fps, 10), 120),
		Seed:      seed,
	}
	if opts.Seed == 0 {
		opts.Seed = rand.Uint64()
	}

	found := false
	for _, s := range sim.Scenes {
		if s.Short() == sceneFlag {
			opts.Scene, found = s, true
		}
	}
	if !found {
		return fmt.Errorf("unknown scene %q; want one of %s", sceneFlag, strings.Join(sceneNames, ", "))
	}
	if opts.Theme = render.ThemeNamed(themeFlag); opts.Theme == nil {
		return fmt.Errorf("unknown theme %q; want one of %s", themeFlag, strings.Join(themeNames, ", "))
	}
	found = false
	for _, m := range render.Modes {
		if m.String() == viewFlag {
			opts.Mode, found = m, true
		}
	}
	if !found {
		return fmt.Errorf("unknown view %q; want one of %s", viewFlag, strings.Join(modeNames, ", "))
	}

	m := ui.New(opts)
	defer m.Close()
	_, err := tea.NewProgram(m, tea.WithFPS(opts.FPS)).Run()
	return err
}
