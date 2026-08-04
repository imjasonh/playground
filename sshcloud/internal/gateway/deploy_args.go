package gateway

import (
	"fmt"
	"strings"

	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// DeployArgs is a non-interactive deploy (`ssh deploy@host fortune --image=…`).
type DeployArgs struct {
	Name     string
	Image    string
	Tier     string // tiny|small; default tiny
	Strategy string // drain|kick; default drain
	Yes      bool   // skip update confirmation
}

// ParseDeployArgs parses exec argv after `ssh deploy@host -- …`.
//
//	fortune --image=repo@sha256:… [--tier=tiny] [--strategy=kick|drain] [--yes]
func ParseDeployArgs(argv []string) (DeployArgs, error) {
	var a DeployArgs
	if len(argv) == 0 {
		return a, fmt.Errorf("usage: fortune --image=repo@sha256:… [--tier=tiny] [--strategy=kick|drain] [--yes]")
	}
	a.Name = argv[0]
	if err := names.ValidateIdent(a.Name); err != nil {
		return a, err
	}
	for _, raw := range argv[1:] {
		arg := raw
		switch {
		case arg == "--yes" || arg == "-y":
			a.Yes = true
		case strings.HasPrefix(arg, "--image="):
			a.Image = strings.TrimSpace(strings.TrimPrefix(arg, "--image="))
		case arg == "--image" || arg == "-image":
			return a, fmt.Errorf("--image requires --image=repo@sha256:…")
		case strings.HasPrefix(arg, "--tier="):
			a.Tier = strings.ToLower(strings.TrimSpace(strings.TrimPrefix(arg, "--tier=")))
		case strings.HasPrefix(arg, "--strategy="):
			a.Strategy = strings.ToLower(strings.TrimSpace(strings.TrimPrefix(arg, "--strategy=")))
		default:
			return a, fmt.Errorf("unknown deploy arg %q", raw)
		}
	}
	if a.Image == "" {
		return a, fmt.Errorf("--image=repo@sha256:… is required")
	}
	if err := image.ValidateDigestPinned(a.Image); err != nil {
		return a, err
	}
	if a.Tier == "" {
		a.Tier = "tiny"
	}
	if a.Tier != "tiny" && a.Tier != "small" {
		return a, fmt.Errorf("tier must be tiny or small")
	}
	switch a.Strategy {
	case "":
		a.Strategy = store.StrategyDrain
	case "drain", "1":
		a.Strategy = store.StrategyDrain
	case "kick", "2":
		a.Strategy = store.StrategyKick
	default:
		return a, fmt.Errorf("strategy must be drain or kick")
	}
	return a, nil
}
