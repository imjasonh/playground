// Command genuca writes a user CA keypair for kvm e2e rootfs injection.
package main

import (
	"flag"
	"log"
	"os"

	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

func main() {
	out := flag.String("out", "ssh_user_ca", "private key path (.pub written alongside)")
	flag.Parse()
	ca, err := userca.LoadOrGenerate(*out)
	if err != nil {
		log.Fatal(err)
	}
	pub := *out + ".pub"
	if err := os.WriteFile(pub, ca.PublicAuthorizedKey(), 0o644); err != nil {
		log.Fatal(err)
	}
	log.Printf("wrote %s and %s", *out, pub)
}
