package main

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"time"

	"chainguard.dev/apko/pkg/build"
	"chainguard.dev/apko/pkg/build/types"
)

// helperCommand is the argument that runs the binary as the build step that
// installs packages and writes layers, instead of as the frontend.
const helperCommand = "build-layers"

// planFile is the file in the helper's output that describes its layers.
const planFile = "plan.json"

// plan tells the frontend what the helper wrote.
type plan struct {
	// Created is the image creation time apko would use: SOURCE_DATE_EPOCH
	// when set, otherwise the newest package build time.
	Created time.Time   `json:"created"`
	Layers  []planLayer `json:"layers"`
}

type planLayer struct {
	// File is the layer's tar file, relative to the output directory.
	File string `json:"file"`
	// Packages names the packages in the layer. The top layer of a
	// layered build has none.
	Packages []string `json:"packages,omitempty"`
}

func runHelper(ctx context.Context, args []string) error {
	fs := flag.NewFlagSet(helperCommand, flag.ContinueOnError)
	configPath := fs.String("config", "", "apko configuration, as JSON")
	lockPath := fs.String("lock", "", "apko lock to install from; without one, apko resolves the configuration's pinned packages")
	arch := fs.String("arch", "", "apk architecture to build")
	fetchDir := fs.String("fetch", "", "directory of files the frontend fetched, named by URL")
	outDir := fs.String("out", "", "directory to write layers and "+planFile+" to")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if *configPath == "" || *arch == "" || *fetchDir == "" || *outDir == "" {
		return errors.New("-config, -arch, -fetch, and -out are required")
	}
	data, err := os.ReadFile(*configPath)
	if err != nil {
		return err
	}
	var ic types.ImageConfiguration
	if err := json.Unmarshal(data, &ic); err != nil {
		return fmt.Errorf("parsing %s: %w", *configPath, err)
	}
	p, err := buildLayers(ctx, ic, types.ParseArchitecture(*arch), *lockPath, *fetchDir, *outDir)
	if err != nil {
		return err
	}
	out, err := json.MarshalIndent(p, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(*outDir, planFile), out, 0o644)
}

// buildLayers runs apko's build, serving every HTTP request from fetchDir,
// and writes apko's layers to outDir as tar files. With a lock, apko installs
// the locked packages. Without one, it resolves ic, whose packages the
// frontend pinned, as apko build does after locking.
func buildLayers(ctx context.Context, ic types.ImageConfiguration, arch types.Architecture, lockPath, fetchDir, outDir string) (*plan, error) {
	var opts []build.Option
	if lockPath != "" {
		opts = append(opts, build.WithLockFile(lockPath))
	}
	bc, err := newBuildContext(ctx, ic, arch, dirTransport{dir: fetchDir}, opts...)
	if err != nil {
		return nil, err
	}
	p := &plan{}
	if layered(ic) {
		plans, content, err := bc.PlanLayers(ctx)
		if err != nil {
			return nil, err
		}
		for i, lp := range plans {
			name := fmt.Sprintf("layer-%d.tar.gz", i)
			if err := writeLayerFile(filepath.Join(outDir, name), func(w io.Writer) error {
				_, err := lp.Render(ctx, content, w)
				return err
			}); err != nil {
				return nil, err
			}
			l := planLayer{File: name}
			for _, pkg := range lp.Packages() {
				l.Packages = append(l.Packages, pkg.Name)
			}
			p.Layers = append(p.Layers, l)
		}
	} else {
		_, layer, err := bc.BuildLayer(ctx)
		if err != nil {
			return nil, err
		}
		name := "layer-0.tar"
		if err := writeLayerFile(filepath.Join(outDir, name), func(w io.Writer) error {
			rc, err := layer.Uncompressed()
			if err != nil {
				return err
			}
			defer rc.Close()
			_, err = io.Copy(w, rc)
			return err
		}); err != nil {
			return nil, err
		}
		p.Layers = append(p.Layers, planLayer{File: name})
	}
	if p.Created, err = bc.GetBuildDateEpoch(); err != nil {
		return nil, err
	}
	return p, nil
}

// layered reports whether apko splits the image into one layer per package
// group plus a top layer.
func layered(ic types.ImageConfiguration) bool {
	return ic.Layering != nil && (ic.Layering.Strategy != "" || ic.Layering.Budget != 0)
}

func writeLayerFile(name string, write func(io.Writer) error) error {
	f, err := os.Create(name)
	if err != nil {
		return err
	}
	if err := write(f); err != nil {
		f.Close()
		return fmt.Errorf("writing %s: %w", name, err)
	}
	return f.Close()
}
