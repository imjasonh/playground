// Package images names the images that the Pods of git-k8s's programs run
// by default.
//
// The defaults name Chainguard's images by digest, so whoever can move a
// tag, such as the registry or a mirror between it and the cluster, can't
// change what runs in a container that holds a repository's credentials.
// To move a default to a newer image, set it to the digest that
// crane digest cgr.dev/chainguard/NAME:latest prints.
package images

const (
	// Git is the default image that fetches a repository. It has git and
	// sh.
	Git = "cgr.dev/chainguard/git@sha256:904bddb55fd9772f9950412408b04d40ef6529e464d77c6b4812dc9fd86a1316"
	// Go is the default image that runs the go command.
	Go = "cgr.dev/chainguard/go@sha256:97450c7109ceb180919daaad0fa464e09f6522388247a39e8a0d17c882508335"
)
