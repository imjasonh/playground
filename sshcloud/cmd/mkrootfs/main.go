// Command mkrootfs builds a fortune ext4 rootfs for Firecracker.
package main

import (
	"flag"
	"log"
	"os"

	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
)

func main() {
	out := flag.String("out", "fortune-rootfs.ext4", "output ext4 path")
	fortuneBin := flag.String("fortune", "", "guest fortune binary (linux)")
	caPub := flag.String("ca-pub", "", "platform user CA public key file")
	size := flag.Int("size-mb", 64, "image size in MiB")
	flag.Parse()
	if *fortuneBin == "" || *caPub == "" {
		log.Fatal("-fortune and -ca-pub are required")
	}
	ca, err := os.ReadFile(*caPub)
	if err != nil {
		log.Fatal(err)
	}
	if err := rootfs.BuildFortune(*out, rootfs.FortuneSpec{
		FortuneBin: *fortuneBin,
		CAPub:      ca,
		SizeMB:     *size,
	}); err != nil {
		log.Fatal(err)
	}
	log.Printf("wrote %s", *out)
}
