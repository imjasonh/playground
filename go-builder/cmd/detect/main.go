package main

import (
	"fmt"
	"os"

	"github.com/imjasonh/playground/go-builder/internal/cnb"
	"github.com/imjasonh/playground/go-builder/internal/detect"
)

func main() {
	env, err := cnb.LoadDetectEnv(os.Args[1:])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	res, err := detect.Run(env)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if !res.Pass {
		fmt.Fprintln(os.Stderr, "---> "+res.Reason)
		os.Exit(100) // CNB fail detect
	}
	if err := detect.WritePlan(env.BuildPlanPath, res.PlanTOML); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "---> playground/go: detected "+res.Reason)
}
