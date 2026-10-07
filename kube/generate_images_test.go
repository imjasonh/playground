//go:build !kube_nogenerate

package kube

import (
	"bytes"
	"encoding/json"
	"flag"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

func TestSetFlags(t *testing.T) {
	fs := flag.NewFlagSet("", flag.ContinueOnError)
	fs.String("go-image", "", "")
	fs.String("git-image", "", "")
	fs.String("model", "", "")
	fs.Bool("dry-run", false, "")
	values := map[string]string{"go-image": "go@D", "git-image": "git@D"}
	for _, tt := range []struct {
		args, want []string
	}{
		{nil, []string{"-git-image=git@D", "-go-image=go@D"}},
		{[]string{"-go-image=go:1"}, []string{"-go-image=go@D", "-git-image=git@D"}},
		{[]string{"--go-image", "go:1", "-model", "m1"}, []string{"--go-image=go@D", "-model", "m1", "-git-image=git@D"}},
		{[]string{"-go-image=go:1", "-git-image", "git:1", "-go-image", "go:2"}, []string{"-go-image=go@D", "-git-image=git@D", "-go-image=go@D"}},
		// A bool flag doesn't take the next argument, and the flags end
		// at the first argument that isn't one, or at "--" or "-".
		{[]string{"-dry-run", "rest", "-go-image=go:1"}, []string{"-dry-run", "-git-image=git@D", "-go-image=go@D", "rest", "-go-image=go:1"}},
		{[]string{"-model=m1", "--", "-go-image=go:1"}, []string{"-model=m1", "-git-image=git@D", "-go-image=go@D", "--", "-go-image=go:1"}},
		{[]string{"-dry-run=false", "-", "-go-image=go:1"}, []string{"-dry-run=false", "-git-image=git@D", "-go-image=go@D", "-", "-go-image=go:1"}},
		// A flag that isn't the last argument takes the next one as its
		// value, even if it starts with "-".
		{[]string{"-model", "-go-image=go:1"}, []string{"-model", "-go-image=go:1", "-git-image=git@D", "-go-image=go@D"}},
	} {
		if got := setFlags(tt.args, fs, values); !slices.Equal(got, tt.want) {
			t.Errorf("setFlags(%q) = %q, want %q", tt.args, got, tt.want)
		}
	}
}

func TestGeneratePinsImageFlags(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	agentDigest := imagetest.Base(t, reg+"/agent:v1", "linux/amd64")
	goDigest := imagetest.Base(t, reg+"/go:v1", "linux/arm64")
	commandLine(t)
	agent := Image("agent-image", "", "image that runs the agent")
	goImage := Image("go-image", reg+"/go:v1", "image that runs go test")
	gitImage := Image("git-image", "registry.invalid/git@"+testDigest, "image that runs git")
	empty := Image("empty-image", "", "optional image")
	flag.String("model", "", "model for the agent")
	flag.Bool("dry-run", false, "print what the agent would do")

	var stderr bytes.Buffer
	o := &generateOptions{args: []string{"-dry-run", "-agent-image", reg + "/agent:v1", "-model", "m1", "--", "rest"}, stderr: &stderr}
	if err := o.parseProgramFlags(); err != nil {
		t.Fatal(err)
	}
	if err := o.pinImageFlags(t.Context()); err != nil {
		t.Fatal(err)
	}
	agentPinned, goPinned := reg+"/agent@"+agentDigest, reg+"/go@"+goDigest
	// -dry-run is a bool flag, so it doesn't take -agent-image as its value.
	want := []string{"-dry-run", "-agent-image=" + agentPinned, "-model", "m1", "-go-image=" + goPinned, "--", "rest"}
	if !slices.Equal(o.args, want) {
		t.Errorf("the Deployment's args = %q, want %q", o.args, want)
	}
	if *agent != agentPinned || *goImage != goPinned || *gitImage != "registry.invalid/git@"+testDigest || *empty != "" {
		t.Errorf("-agent-image=%q, -go-image=%q, -git-image=%q, -empty-image=%q", *agent, *goImage, *gitImage, *empty)
	}
	wantLog := "resolved -agent-image=" + reg + "/agent:v1 to " + agentPinned + "\n" +
		"resolved -go-image=" + reg + "/go:v1 to " + goPinned + "\n"
	if stderr.String() != wantLog {
		t.Errorf("stderr = %q, want %q", stderr.String(), wantLog)
	}
}

// TestGenerateFailsOnImageFlagThatDoesNotResolve checks that generate
// resolves the image flags before it builds the program, and writes no YAML
// when a tag doesn't resolve.
func TestGenerateFailsOnImageFlagThatDoesNotResolve(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/agent:v1", "linux/amd64")
	commandLine(t)
	Image("agent-image", reg+"/agent:nope", "image that runs the agent")
	flag.String("model", "", "model for the agent")

	var stdout bytes.Buffer
	args := []string{"-registry=" + reg, "-platform=linux/amd64", "--", "-model", "m1"}
	err := (&Manager{}).generate(t.Context(), args, nil, &stdout, new(bytes.Buffer))
	if want := "generate: -agent-image: resolving image " + reg + "/agent:nope: "; err == nil || !strings.HasPrefix(err.Error(), want) {
		t.Errorf("generate %q = %v, want an error that starts %q", args, err, want)
	}
	if stdout.Len() > 0 {
		t.Errorf("generate wrote %q, want nothing", stdout.String())
	}
}

func TestGeneratePinsImagesInManifests(t *testing.T) {
	t.Setenv("DOCKER_CONFIG", t.TempDir())
	reg := imagetest.Registry(t)
	digest := imagetest.Base(t, reg+"/prog:v1", "linux/amd64")
	var stderr bytes.Buffer
	o := &generateOptions{program: "prog", name: "prog", namespace: "prog", replicas: 1, shards: 1, stderr: &stderr}
	p := &installPlan{cluster: grants{}, local: grants{}}

	docs := o.manifests(reg+"/prog:v1", p)
	if err := o.pinImages(t.Context(), docs); err != nil {
		t.Fatal(err)
	}
	b, _ := json.Marshal(docs[len(docs)-1])
	if want := `"image":"` + reg + `/prog@` + digest + `"`; !strings.Contains(string(b), want) {
		t.Errorf("the Deployment lacks %s: %s", want, b)
	}
	if want := "resolved " + reg + "/prog:v1 to " + reg + "/prog@" + digest + "\n"; stderr.String() != want {
		t.Errorf("stderr = %q, want %q", stderr.String(), want)
	}

	docs = o.manifests(reg+"/prog:nope", p)
	err := o.pinImages(t.Context(), docs)
	if want := "generate: Deployment prog: container prog: resolving image " + reg + "/prog:nope: "; err == nil || !strings.HasPrefix(err.Error(), want) {
		t.Errorf("pinImages() = %v, want an error that starts %q", err, want)
	}
}
