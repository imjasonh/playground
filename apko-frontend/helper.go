package main

import (
	"archive/tar"
	"bufio"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
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
	lockPath := fs.String("lock", "", "apko lock that pins the packages to install")
	arch := fs.String("arch", "", "apk architecture to build")
	fetchDir := fs.String("fetch", "", "directory of files the frontend fetched, named by URL")
	outDir := fs.String("out", "", "directory to write layers and "+planFile+" to")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if *configPath == "" || *lockPath == "" || *arch == "" || *fetchDir == "" || *outDir == "" {
		return errors.New("-config, -lock, -arch, -fetch, and -out are required")
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

// buildLayers runs apko's build of the locked packages, serving every HTTP
// request from fetchDir, and writes apko's layers to outDir as tar files.
func buildLayers(ctx context.Context, ic types.ImageConfiguration, arch types.Architecture, lockPath, fetchDir, outDir string) (*plan, error) {
	// apko expands packages and writes layers in temporary directories.
	// Keep them in outDir, which is on disk, rather than in a tmpfs that
	// holds the whole image in memory, and remove them before BuildKit
	// snapshots outDir.
	tmp, err := os.MkdirTemp(outDir, ".tmp-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(tmp)
	if old, ok := os.LookupEnv("TMPDIR"); ok {
		defer os.Setenv("TMPDIR", old)
	} else {
		defer os.Unsetenv("TMPDIR")
	}
	if err := os.Setenv("TMPDIR", tmp); err != nil {
		return nil, err
	}
	bc, err := newBuildContext(ctx, ic, arch, dirTransport{dir: fetchDir}, build.WithLockFile(lockPath), build.WithTempDir(tmp))
	if err != nil {
		return nil, err
	}
	// BuildLayers writes uncompressed tars. BuildKit unpacks each one and
	// compresses the layer itself when it exports the image, so a
	// compressed tar here would only add a compression and a
	// decompression.
	layers, err := bc.BuildLayers(ctx)
	if err != nil {
		return nil, err
	}
	p := &plan{}
	for i, layer := range layers {
		name := fmt.Sprintf("layer-%d.tar", i)
		path := filepath.Join(outDir, name)
		if err := writeFile(path, func(w io.Writer) error {
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
		l := planLayer{File: name}
		// In a layered build, each layer but the top one holds one
		// package group and an installed database of just its packages.
		if layered(ic) && i < len(layers)-1 {
			if l.Packages, err = installedPackages(path); err != nil {
				return nil, err
			}
		}
		p.Layers = append(p.Layers, l)
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

// installedPackages returns the names of the packages in the installed
// database of the layer tar at path.
func installedPackages(path string) ([]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	// tar.Reader seeks past file contents when it can, so finding the
	// database reads little more than the headers.
	tr := tar.NewReader(f)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			return nil, nil
		} else if err != nil {
			return nil, fmt.Errorf("reading %s: %w", path, err)
		}
		if strings.TrimLeft(hdr.Name, "./") != installedDB {
			continue
		}
		var names []string
		sc := bufio.NewScanner(tr)
		sc.Buffer(make([]byte, 64<<10), 1<<20)
		for sc.Scan() {
			if name, ok := strings.CutPrefix(sc.Text(), "P:"); ok {
				names = append(names, name)
			}
		}
		return names, sc.Err()
	}
}

// installedDB is the path of apk's installed database in apko's layers.
const installedDB = "usr/lib/apk/db/installed"

func writeFile(name string, write func(io.Writer) error) error {
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
