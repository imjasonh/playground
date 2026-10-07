package kube

import (
	"cmp"
	"context"
	"flag"
	"fmt"
	"log/slog"
	"strings"
	"sync"

	"github.com/imjasonh/playground/kube/internal/registry"
)

// Image defines a flag with the given name, default value, and usage that
// names a container image, and returns the address of a string variable
// that stores the flag's value. See ImageVar.
func Image(name, value, usage string) *string {
	p := new(string)
	ImageVar(flag.CommandLine, p, name, value, usage)
	return p
}

// ImageVar defines a flag on fs with the given name, default value, and
// usage that names a container image, and stores the flag's value in p. The
// flag takes an image reference, such as "cgr.dev/chainguard/git@sha256:...",
// or an empty string.
//
// Name images by digest where you can. If an image flag on flag.CommandLine
// names an image by tag, generate resolves the tag, and sets the flag to the
// image by digest in the Deployment's arguments. Before it starts any
// controller, Run resolves a tag that's still there and sets the flag to the
// image by digest, or fails if it can't, so the program uses one image for
// the flag while it runs.
func ImageVar(fs *flag.FlagSet, p *string, name, value, usage string) {
	*p = value
	fs.Var((*imageValue)(p), name, usage)
}

// imageValue is the value of an image flag.
type imageValue string

func (v *imageValue) String() string {
	if v == nil {
		return ""
	}
	return string(*v)
}

func (v *imageValue) Set(s string) error {
	if s != "" {
		if _, err := registry.Parse(s); err != nil {
			return err
		}
	}
	*v = imageValue(s)
	return nil
}

// images resolves the tags in the program's image flags and in the
// containers of the objects that it applies.
var images = &imageDigests{digest: registry.Digest}

// imageDigests resolves image tags to digests with digest. It resolves each
// tag once, and keeps the digest while the program runs, so every object
// that names the tag gets the same image.
type imageDigests struct {
	digest func(ctx context.Context, ref string) (string, error)

	mu    sync.Mutex
	calls map[string]*imageCall
}

// imageCall resolves one tag, for the callers that ask for it meanwhile,
// and, if it succeeds, for those that ask later.
type imageCall struct {
	done   chan struct{}
	digest string
	err    error
}

// pin returns ref, an image reference, by digest, with the repository as
// ref writes it. If ref has a digest, pin returns ref. resolved reports
// whether pin asked the registry for the digest of ref's tag.
func (d *imageDigests) pin(ctx context.Context, ref string) (pinned string, resolved bool, err error) {
	r, err := registry.Parse(ref)
	if err != nil {
		return "", false, fmt.Errorf("image %q: %w", ref, err)
	}
	if r.Digest != "" {
		return ref, false, nil
	}
	key := r.Registry + "/" + r.Repository + ":" + cmp.Or(r.Tag, "latest")
	d.mu.Lock()
	c, found := d.calls[key]
	if !found {
		c = &imageCall{done: make(chan struct{})}
		if d.calls == nil {
			d.calls = map[string]*imageCall{}
		}
		d.calls[key] = c
	}
	d.mu.Unlock()
	if !found {
		c.digest, c.err = d.digest(ctx, ref)
		if c.err != nil {
			c.err = fmt.Errorf("resolving image %s: %w", ref, c.err)
			// The next caller tries again.
			d.mu.Lock()
			delete(d.calls, key)
			d.mu.Unlock()
		}
		close(c.done)
	}
	select {
	case <-c.done:
	case <-ctx.Done():
		return "", false, ctx.Err()
	}
	if c.err != nil {
		return "", false, c.err
	}
	return r.WithDigest(c.digest), !found, nil
}

// pinFlags sets each image flag on fs that names a tag to the image by
// digest, and calls resolved for each. It returns the values that it set,
// by flag name.
func (d *imageDigests) pinFlags(ctx context.Context, fs *flag.FlagSet, resolved func(name, from, to string)) (map[string]string, error) {
	var flags []*flag.Flag
	fs.VisitAll(func(f *flag.Flag) {
		if v, ok := f.Value.(*imageValue); ok && *v != "" {
			flags = append(flags, f)
		}
	})
	pinned := map[string]string{}
	for _, f := range flags {
		v := f.Value.(*imageValue)
		from := string(*v)
		to, _, err := d.pin(ctx, from)
		if err != nil {
			return nil, fmt.Errorf("-%s: %w", f.Name, err)
		}
		if to != from {
			*v = imageValue(to)
			pinned[f.Name] = to
			resolved(f.Name, from, to)
		}
	}
	return pinned, nil
}

// podSpecs are the paths to the Pod specs of the objects whose containers
// kube resolves the images of, by kind, with the API group and a slash
// before a kind outside the core group.
var podSpecs = map[string][]string{
	"Pod":                   {"spec"},
	"PodTemplate":           {"template", "spec"},
	"ReplicationController": {"spec", "template", "spec"},
	"apps/DaemonSet":        {"spec", "template", "spec"},
	"apps/Deployment":       {"spec", "template", "spec"},
	"apps/ReplicaSet":       {"spec", "template", "spec"},
	"apps/StatefulSet":      {"spec", "template", "spec"},
	"batch/CronJob":         {"spec", "jobTemplate", "spec", "template", "spec"},
	"batch/Job":             {"spec", "template", "spec"},
}

// A jsonObject is a JSON object that pinImages reads and changes: a
// map[string]any, or an object that generate writes.
type jsonObject interface {
	get(key string) any
	set(key string, value any)
}

type jsonMap map[string]any

func (m jsonMap) get(key string) any        { return m[key] }
func (m jsonMap) set(key string, value any) { m[key] = value }

func asObject(v any) (jsonObject, bool) {
	switch v := v.(type) {
	case map[string]any:
		return jsonMap(v), true
	case jsonObject:
		return v, true
	}
	return nil, false
}

// pinImages replaces each image that names a tag in the init, regular, and
// ephemeral containers of obj, if obj is a Pod or has a Pod template, with
// the image by digest. It calls resolved for each tag that it resolves.
func (d *imageDigests) pinImages(ctx context.Context, obj jsonObject, resolved func(from, to string)) error {
	apiVersion, _ := obj.get("apiVersion").(string)
	kind, _ := obj.get("kind").(string)
	if group, _, ok := strings.Cut(apiVersion, "/"); ok {
		kind = group + "/" + kind
	}
	path, ok := podSpecs[kind]
	spec := obj
	for i := 0; ok && i < len(path); i++ {
		spec, ok = asObject(spec.get(path[i]))
	}
	if !ok {
		return nil
	}
	for _, list := range []string{"initContainers", "containers", "ephemeralContainers"} {
		containers, _ := spec.get(list).([]any)
		for _, c := range containers {
			container, ok := asObject(c)
			if !ok {
				continue
			}
			from, _ := container.get("image").(string)
			if from == "" {
				continue
			}
			to, did, err := d.pin(ctx, from)
			if err != nil {
				name, _ := container.get("name").(string)
				return fmt.Errorf("container %s: %w", name, err)
			}
			if to != from {
				container.set("image", to)
			}
			if did {
				resolved(from, to)
			}
		}
	}
	return nil
}

// resolveImageFlags resolves the tags in the image flags on flag.CommandLine.
func (m *Manager) resolveImageFlags(ctx context.Context) error {
	_, err := images.pinFlags(ctx, flag.CommandLine, func(name, from, to string) {
		m.log.Info("resolved image flag", "flag", name, "image", from, "pinned", to)
	})
	return err
}

// resolveImages resolves the tags of the images in the containers of obj,
// an object to apply.
func resolveImages(ctx context.Context, obj map[string]any, log *slog.Logger) error {
	return images.pinImages(ctx, jsonMap(obj), func(from, to string) {
		log.Info("resolved image", "image", from, "pinned", to)
	})
}
