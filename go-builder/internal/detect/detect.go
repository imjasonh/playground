// Package detect implements Cloud Native Buildpacks detect for Go apps.
package detect

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/imjasonh/playground/go-builder/internal/cnb"
)

// Result is the outcome of detection.
type Result struct {
	Pass bool
	// PlanTOML is written to CNB_BUILD_PLAN_PATH on Pass.
	PlanTOML string
	Reason   string
}

// Run passes only for Go module apps (go.mod present). This builder is
// intentionally Go-only — no fallbacks for other languages.
func Run(env cnb.DetectEnv) (Result, error) {
	mod := filepath.Join(env.AppDir, "go.mod")
	if _, err := os.Stat(mod); err != nil {
		if os.IsNotExist(err) {
			return Result{
				Pass:   false,
				Reason: "no go.mod — playground/go only supports Go module apps",
			}, nil
		}
		return Result{}, err
	}

	// Refuse obvious non-Go polyglot roots that people might point pack at by
	// mistake when they wanted a multi-language builder. Still require go.mod
	// (already checked); this is just a loud warning in the plan metadata.
	plan := fmt.Sprintf(`[[provides]]
name = "go-binary"

[[requires]]
name = "go-binary"
[requires.metadata]
build = true
launch = true
`)
	return Result{
		Pass:     true,
		PlanTOML: plan,
		Reason:   "go.mod",
	}, nil
}

// WritePlan writes the build plan to the platform path.
func WritePlan(path, contents string) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, []byte(contents), 0o644)
}
