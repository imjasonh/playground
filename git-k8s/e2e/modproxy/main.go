// Command modproxy serves Go modules from a directory over the module proxy
// protocol, for the end-to-end test. go-cache uses it as its upstream, so
// test Pods get their dependencies without the internet. It logs each
// request, which shows when go-cache served a module from its own store.
//
// Each module version is a directory named MODULE@VERSION, such as
// example.com/greet@v1.0.0, under -dir.
package main

import (
	"archive/zip"
	"encoding/json"
	"flag"
	"fmt"
	"io/fs"
	"log"
	"net"
	"net/http"
	"os"
	"path"
	"path/filepath"
	"slices"
	"strings"
	"time"
)

func main() {
	addr := flag.String("addr", "127.0.0.1:0", "address to serve on")
	dir := flag.String("dir", "", "directory that holds the module versions")
	flag.Parse()
	if *dir == "" {
		log.Fatal("set -dir")
	}
	ln, err := net.Listen("tcp", *addr)
	if err != nil {
		log.Fatal(err)
	}
	log.Printf("serving %s on %s", *dir, ln.Addr())
	srv := &http.Server{
		Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			log.Printf("%s %s %d", r.Method, r.URL.Path, serve(w, r, *dir))
		}),
		ReadHeaderTimeout: 10 * time.Second,
	}
	log.Fatal(srv.Serve(ln))
}

// serve answers a module proxy request, and returns the status.
func serve(w http.ResponseWriter, r *http.Request, root string) int {
	module, file, ok := strings.Cut(strings.TrimPrefix(r.URL.Path, "/"), "/@")
	if !ok || r.Method != http.MethodGet || !fs.ValidPath(module) {
		http.NotFound(w, r)
		return http.StatusNotFound
	}
	versions := versions(root, module)
	if file == "v/list" {
		for _, v := range versions {
			fmt.Fprintln(w, v)
		}
		return http.StatusOK
	}
	version, ext := "", ".info"
	if file == "latest" && len(versions) > 0 {
		version = versions[len(versions)-1]
	} else if name, ok := strings.CutPrefix(file, "v/"); ok {
		ext = path.Ext(name)
		version = strings.TrimSuffix(name, ext)
	}
	if !slices.Contains(versions, version) {
		http.Error(w, "not found", http.StatusGone)
		return http.StatusGone
	}
	dir := filepath.Join(root, filepath.FromSlash(module)+"@"+version)
	switch ext {
	case ".info":
		json.NewEncoder(w).Encode(map[string]string{"Version": version, "Time": "2026-01-01T00:00:00Z"})
	case ".mod":
		http.ServeFile(w, r, filepath.Join(dir, "go.mod"))
	case ".zip":
		if err := writeZip(w, dir, module+"@"+version); err != nil {
			log.Printf("zipping %s: %v", dir, err)
		}
	default:
		http.NotFound(w, r)
		return http.StatusNotFound
	}
	return http.StatusOK
}

// versions lists the versions of module under root, sorted as strings,
// which is enough for the test's modules.
func versions(root, module string) []string {
	matches, _ := filepath.Glob(filepath.Join(root, filepath.FromSlash(module)+"@v*"))
	var vs []string
	for _, m := range matches {
		vs = append(vs, strings.TrimPrefix(filepath.Base(m), path.Base(module)+"@"))
	}
	slices.Sort(vs)
	return vs
}

// writeZip writes the files in dir as a module zip, under prefix.
func writeZip(w http.ResponseWriter, dir, prefix string) error {
	w.Header().Set("Content-Type", "application/zip")
	zw := zip.NewWriter(w)
	if err := filepath.WalkDir(dir, func(p string, d fs.DirEntry, err error) error {
		if err != nil || !d.Type().IsRegular() {
			return err
		}
		rel, err := filepath.Rel(dir, p)
		if err != nil {
			return err
		}
		b, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		f, err := zw.Create(prefix + "/" + filepath.ToSlash(rel))
		if err != nil {
			return err
		}
		_, err = f.Write(b)
		return err
	}); err != nil {
		return err
	}
	return zw.Close()
}
