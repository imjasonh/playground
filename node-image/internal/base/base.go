package base

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"
)

// Info describes a base image for validation.
type Info struct {
	Ref          string
	DigestPinned bool
	LayerCount   int
	NodeMajor    int    // 0 if unknown
	NodeMinor    int    // 0 if unknown
	Libc         string // "glibc", "musl", or "" if unknown
	Warnings     []string
}

var (
	nodeVersionEnv = regexp.MustCompile(`(?i)^NODE_VERSION=v?(\d+)(?:\.(\d+))?`)
	nodeInRef      = regexp.MustCompile(`(?i)nodejs?(\d+)`)
	shaDigest      = regexp.MustCompile(`@sha256:[a-f0-9]{64}$`)
)

// Inspect pulls base config (manifest+config only for layer count) and infers Node/libc.
func Inspect(ref string, platform v1.Platform) (*Info, error) {
	info := &Info{Ref: ref, DigestPinned: shaDigest.MatchString(ref)}
	if !info.DigestPinned {
		info.Warnings = append(info.Warnings,
			fmt.Sprintf("base %q is not pinned by digest; rebuilds may not be reproducible (prefer base@sha256:…)", ref))
	}

	r, err := name.ParseReference(ref, name.WeakValidation)
	if err != nil {
		return nil, fmt.Errorf("invalid base image %q: %w\nHint: use a registry reference like gcr.io/distroless/nodejs22-debian12", ref, err)
	}
	img, err := remote.Image(r, remote.WithAuthFromKeychain(authn.DefaultKeychain), remote.WithPlatform(platform))
	if err != nil {
		return nil, fmt.Errorf("pull base %s: %w\nHint: check the name/tag exists and you are authenticated if it is private", ref, err)
	}
	layers, err := img.Layers()
	if err != nil {
		return nil, err
	}
	info.LayerCount = len(layers)

	cfg, err := img.ConfigFile()
	if err != nil {
		return nil, err
	}
	info.NodeMajor, info.NodeMinor = detectNodeVersion(cfg, ref)
	info.Libc = DetectLibc(ref, cfg)
	return info, nil
}

// DetectLibc infers glibc vs musl from the image reference and config hints.
func DetectLibc(ref string, cfg *v1.ConfigFile) string {
	return detectLibc(cfg, ref)
}

// ScratchInfo is used with --empty-base / scratch.
func ScratchInfo() *Info {
	return &Info{Ref: "scratch", DigestPinned: true, LayerCount: 0, Libc: "glibc"}
}

func detectNodeVersion(cfg *v1.ConfigFile, ref string) (major, minor int) {
	if cfg != nil {
		for _, e := range cfg.Config.Env {
			if m := nodeVersionEnv.FindStringSubmatch(e); m != nil {
				major, _ = strconv.Atoi(m[1])
				if len(m) > 2 && m[2] != "" {
					minor, _ = strconv.Atoi(m[2])
				}
				return major, minor
			}
		}
		// Some images set NODE_MAJOR_VERSION=22
		for _, e := range cfg.Config.Env {
			if strings.HasPrefix(strings.ToUpper(e), "NODE_MAJOR_VERSION=") {
				v := strings.SplitN(e, "=", 2)[1]
				major, _ = strconv.Atoi(v)
				return major, 0
			}
		}
	}
	if m := nodeInRef.FindStringSubmatch(ref); m != nil {
		major, _ = strconv.Atoi(m[1])
		return major, 0
	}
	return 0, 0
}

func detectLibc(cfg *v1.ConfigFile, ref string) string {
	lower := strings.ToLower(ref)
	switch {
	case strings.Contains(lower, "alpine"):
		return "musl"
	case strings.Contains(lower, "wolfi"), strings.Contains(lower, "chainguard"):
		return "musl"
	case strings.Contains(lower, "debian"), strings.Contains(lower, "ubuntu"), strings.Contains(lower, "distroless"):
		return "glibc"
	}
	if cfg != nil {
		for _, e := range cfg.Config.Env {
			u := strings.ToUpper(e)
			if strings.Contains(u, "ALPINE") {
				return "musl"
			}
		}
	}
	return ""
}

// RequireGlibc fails if the base is musl (or unknown with a musl-looking name already handled).
func RequireGlibc(info *Info) error {
	switch info.Libc {
	case "glibc", "":
		// unknown: warn via caller; allow with warning already collected
		if info.Libc == "" {
			info.Warnings = append(info.Warnings,
				fmt.Sprintf("could not detect libc for base %q; assuming glibc. If this is musl (Alpine/Wolfi/Chainguard), native optional packages may break — pin a debian/distroless Node base", info.Ref))
		}
		return nil
	case "musl":
		return fmt.Errorf("base %q appears to use musl libc, but node-image targets glibc by default\nHint: use a glibc Node base such as gcr.io/distroless/nodejs22-debian12 (or another debian/ubuntu Node image). Musl mode is not supported yet", info.Ref)
	default:
		return fmt.Errorf("base %q has unsupported libc %q", info.Ref, info.Libc)
	}
}

// CheckEngines validates package.json engines.node against the base when both are known.
func CheckEngines(enginesNode string, info *Info) error {
	if enginesNode == "" || info.NodeMajor == 0 {
		return nil
	}
	// Support simple forms: "22", ">=22", "^22", "22.x", ">=18 <23"
	minMajor := parseMinNodeMajor(enginesNode)
	if minMajor == 0 {
		return nil
	}
	if info.NodeMajor < minMajor {
		return fmt.Errorf("base Node %d is older than package engines.node %q (needs >= %d)\nHint: pick a newer Node base (e.g. nodejs%d) or relax engines.node", info.NodeMajor, enginesNode, minMajor, minMajor)
	}
	return nil
}

func parseMinNodeMajor(spec string) int {
	spec = strings.TrimSpace(spec)
	// take first number in the string as a rough minimum
	re := regexp.MustCompile(`(\d+)`)
	m := re.FindStringSubmatch(spec)
	if m == nil {
		return 0
	}
	n, _ := strconv.Atoi(m[1])
	return n
}

// CheckMuslDeps fails if any required package is musl-only while targeting glibc.
func CheckMuslDeps(wantLibc string, muslOnlyPackages []string) error {
	if wantLibc != "glibc" && wantLibc != "" {
		return nil
	}
	if len(muslOnlyPackages) == 0 {
		return nil
	}
	return fmt.Errorf("dependencies require musl-only native artifacts, but the build targets glibc:\n  - %s\nHint: switch those packages to glibc variants, or wait for an explicit --libc musl mode with a matching base", strings.Join(muslOnlyPackages, "\n  - "))
}
