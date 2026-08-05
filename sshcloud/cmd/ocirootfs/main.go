// Command ocirootfs materializes a digest-pinned OCI image into a cached ext4 rootfs.
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"os/signal"
	"syscall"

	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
)

func main() {
	cache := flag.String("cache-dir", "", "digest-addressed ext4 cache directory")
	size := flag.Int("size-mb", 512, "ext4 size in MiB")
	printSpec := flag.Bool("print-spec", false, "also print entrypoint/cmd/env/workingDir JSON to stdout after the path")
	flag.Parse()
	if flag.NArg() != 1 {
		log.Fatal("usage: ocirootfs [-cache-dir DIR] [-size-mb N] [-print-spec] repo@sha256:<64 hex>")
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	res, err := ocirootfs.Materialize(ctx, flag.Arg(0), ocirootfs.Options{
		CacheDir: *cache,
		SizeMB:   *size,
	})
	if err != nil {
		log.Fatal(err)
	}
	if res.Release != nil {
		defer res.Release()
	}
	fmt.Println(res.Rootfs)
	if *printSpec {
		enc := json.NewEncoder(os.Stdout)
		enc.SetIndent("", "  ")
		if err := enc.Encode(res.Spec); err != nil {
			log.Fatal(err)
		}
	}
}
