package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"io"
	"net/url"
	"os"
	"slices"
	"strings"
	"time"

	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/gocache"
	"github.com/imjasonh/playground/git-k8s/internal/images"
)

// goCache is where test Pods download modules and share build outputs,
// when -go-cache is set.
var goCache struct {
	// url is the go-cache server's URL, without a trailing slash.
	url string
}

func init() {
	flag.Func("go-cache", "URL of a go-cache server, such as http://go-cache.go-cache, that test Pods download modules from and share build outputs through, instead of using -goproxy", setGoCache)
}

func setGoCache(s string) error {
	u, err := url.Parse(s)
	if err != nil || (u.Scheme != "http" && u.Scheme != "https") || u.Host == "" || u.RawQuery != "" || u.Fragment != "" {
		return fmt.Errorf("%q isn't an http or https URL", s)
	}
	goCache.url = strings.TrimSuffix(s, "/")
	return nil
}

const (
	// goCacheDir is an emptyDir volume that holds the GOCACHEPROG program
	// and the build outputs.
	goCacheDir    = "/go-cache"
	cacheprogPath = goCacheDir + "/check-gotest"
	outputsDir    = goCacheDir + "/outputs"
	tokenDir      = "/var/run/secrets/go-cache"
	// tokenSeconds is the shortest lifetime that Kubernetes allows for a
	// projected service account token.
	tokenSeconds = 600
)

// addGoCache makes a test Pod download modules from go-cache, and share
// build outputs with other test Pods through the repository's build cache.
//
// fetch runs this binary instead of fetchScript, and installs it as the
// GOCACHEPROG program before it fetches the source; see fetchSource. A git
// bug that ran code from the fetched objects could already change what
// build runs, through the go env file in the tmp volume, so fetch may
// install the program too. Two init containers run after fetch. build
// compiles the packages from GOROOT and the module cache that go test
// needs, with the same toolchain, paths, and environment as the test
// container, reading the build cache with a token whose audience allows
// only reading; see gocache.Build. upload sends what build compiled to
// go-cache, with a token whose audience allows writing. upload never reads
// the branch's files, and none of the branch's code has run yet. The test
// container compiles the module's own packages, gets the rest from the
// go-cache volume, and has neither token, so tests can't change what other
// Pods read.
func addGoCache(p *Pod, in *checks.Input) error {
	if goCache.url == "" {
		return nil
	}
	// generate parses -go-cache too, but only the Deployment that it writes
	// sets KUBE_IMAGE.
	image := os.Getenv("KUBE_IMAGE")
	if image == "" {
		return errors.New("test Pods run check-gotest's own image to use go-cache, so KUBE_IMAGE must name it, as kube's generate does")
	}
	ns, repo := in.Meta.Namespace, in.Repository.Name
	remote := goCache.url + gocache.Path(ns, repo)
	tokenFile := tokenDir + "/token"
	expiry := int64(tokenSeconds)
	token := func(name, audience string) Volume {
		return Volume{Name: name, Projected: &Projected{Sources: []VolumeProjection{{
			ServiceAccountToken: &ServiceAccountTokenProjection{Audience: audience, ExpirationSeconds: &expiry, Path: "token"},
		}}}}
	}
	p.Spec.Volumes = append(p.Spec.Volumes,
		Volume{Name: "go-cache", EmptyDir: &EmptyDir{}},
		token("go-cache-read", gocache.ReadAudience(ns, repo)),
		token("go-cache-write", gocache.WriteAudience(ns, repo)),
	)

	fetch := &p.Spec.InitContainers[0]
	fetch.Image = image
	fetch.ImagePullPolicy = images.PullPolicy(image)
	fetch.Command = nil
	fetch.Args = []string{"fetch", "-dir=/src/repo", "-install=" + cacheprogPath}
	fetch.VolumeMounts = append(slices.Clone(fetch.VolumeMounts), VolumeMount{Name: "go-cache", MountPath: goCacheDir})

	test := &p.Spec.Containers[0]
	setEnv(test, "GOPROXY", goCache.url+"/mod")
	setEnv(test, "GOCACHEPROG", cacheprogPath+" cacheprog -dir="+outputsDir)
	test.VolumeMounts = append(slices.Clone(test.VolumeMounts), VolumeMount{Name: "go-cache", MountPath: goCacheDir})

	build := *test
	build.Name = "build"
	build.Command = []string{cacheprogPath, "cacheprog", "-build", "-dir=" + outputsDir, "-remote=" + remote, "-token-file=" + tokenFile}
	build.Env = slices.Clone(test.Env)
	build.VolumeMounts = append(slices.Clone(test.VolumeMounts), VolumeMount{Name: "go-cache-read", MountPath: tokenDir, ReadOnly: true})

	helper := func(name string, mounts []VolumeMount, args ...string) Container {
		return Container{
			Name:                     name,
			Image:                    image,
			ImagePullPolicy:          images.PullPolicy(image),
			Args:                     append([]string{"cacheprog"}, args...),
			VolumeMounts:             mounts,
			SecurityContext:          test.SecurityContext,
			TerminationMessagePolicy: "FallbackToLogsOnError",
		}
	}
	p.Spec.InitContainers = append(p.Spec.InitContainers,
		build,
		helper("upload", []VolumeMount{
			{Name: "go-cache", MountPath: goCacheDir, ReadOnly: true},
			{Name: "go-cache-write", MountPath: tokenDir, ReadOnly: true},
		}, "-upload", "-dir="+outputsDir, "-remote="+remote, "-token-file="+tokenFile),
	)
	return nil
}

func setEnv(c *Container, name, value string) {
	for i := range c.Env {
		if c.Env[i].Name == name {
			c.Env[i].Value = value
			return
		}
	}
	c.Env = append(c.Env, EnvVar{Name: name, Value: value})
}

// goCacheFailure returns the message of a step that addGoCache added, if
// one failed: fetch's install of the GOCACHEPROG program, build, or upload.
// build fails when the go command does, such as for a go.mod file that
// doesn't parse, and then the test container doesn't run.
func goCacheFailure(pod *Pod) (string, bool) {
	if msg, _, code := terminated(pod.Status.InitContainerStatuses, "fetch"); code == installStatus {
		return "fetch: " + msg, true
	}
	for _, name := range []string{"build", "upload"} {
		if msg, _, code := terminated(pod.Status.InitContainerStatuses, name); code != 0 {
			return name + ": " + msg, true
		}
	}
	return "", false
}

// cacheprog is check-gotest's part in a test Pod after fetch. By default,
// it's the GOCACHEPROG program. With -build, it compiles the packages that
// the Pod can share, and with -upload, it uploads what -build compiled.
func cacheprog(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	flags := flag.NewFlagSet("cacheprog", flag.ContinueOnError)
	flags.SetOutput(stderr)
	build := flags.Bool("build", false, "compile the packages from GOROOT and the module cache that go test needs, sharing their outputs through -dir and -remote, and exit")
	upload := flags.Bool("upload", false, "upload the outputs that the go command built in -dir while -share was set to -remote, and exit")
	dir := flags.String("dir", "", "directory that holds the build outputs")
	remote := flags.String("remote", "", "URL of the repository's build cache on a go-cache server")
	tokenFile := flags.String("token-file", "", "file that holds the service account token for -remote")
	share := flags.Bool("share", false, "record the outputs that the go command builds, for -upload")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	switch {
	case *build:
		exe, err := os.Executable()
		if err != nil {
			fmt.Fprintln(stderr, err)
			return 1
		}
		prog := fmt.Sprintf("%s cacheprog -dir=%s -remote=%s -token-file=%s -share", exe, *dir, *remote, *tokenFile)
		shared, total, err := gocache.Build(context.Background(), prog, stderr)
		if err != nil {
			fmt.Fprintln(stderr, err)
			return 1
		}
		fmt.Fprintf(stdout, "go test needs %d packages; %d are from GOROOT or the module cache, so their outputs go through go-cache\n", total, len(shared))
	case *upload:
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		stored, had, err := gocache.Upload(ctx, nil, *dir, *remote, *tokenFile)
		fmt.Fprintf(stdout, "go-cache stored %d build outputs, and already had %d\n", stored, had)
		if err != nil {
			// The tests run either way.
			fmt.Fprintln(stdout, err)
		}
	default:
		p := &gocache.Prog{Dir: *dir, Remote: *remote, TokenFile: *tokenFile, Share: *share, Log: stderr}
		if err := p.Run(context.Background(), stdin, stdout); err != nil {
			fmt.Fprintln(stderr, err)
			return 1
		}
	}
	return 0
}

// installSelf copies this binary to path, which must not exist.
func installSelf(path string) error {
	exe, err := os.Executable()
	if err != nil {
		return err
	}
	src, err := os.Open(exe)
	if err != nil {
		return err
	}
	defer src.Close()
	dst, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o755)
	if err != nil {
		return err
	}
	_, err = io.Copy(dst, src)
	if cerr := dst.Close(); err == nil {
		err = cerr
	}
	return err
}
