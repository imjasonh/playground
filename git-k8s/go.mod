module github.com/imjasonh/playground/git-k8s

go 1.26.0

// git-k8s builds against the kube framework in this repository at head.
replace github.com/imjasonh/playground/kube => ../kube

require github.com/imjasonh/playground/kube v0.0.0-00010101000000-000000000000

require (
	github.com/docker/cli v29.8.2+incompatible // indirect
	github.com/docker/docker-credential-helpers v0.9.9 // indirect
	github.com/google/go-containerregistry v0.22.1 // indirect
	github.com/klauspost/compress v1.20.1 // indirect
	github.com/opencontainers/go-digest v1.0.0 // indirect
	github.com/opencontainers/image-spec v1.1.1 // indirect
	github.com/sirupsen/logrus v1.10.2 // indirect
	golang.org/x/sync v0.23.0 // indirect
	golang.org/x/sys v0.48.0 // indirect
)
