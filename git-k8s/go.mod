module github.com/imjasonh/playground/git-k8s

go 1.26.0

// git-k8s builds against the kube framework in this repository at head.
replace github.com/imjasonh/playground/kube => ../kube

require (
	cel.dev/cel-go v0.32.0
	github.com/imjasonh/playground/kube v0.0.0-20261004045644-a7ef95f91176
	go.yaml.in/yaml/v3 v3.0.5
	golang.org/x/mod v0.41.0
	golang.org/x/sync v0.23.0
)

require (
	cel.dev/expr v0.25.3 // indirect
	github.com/antlr4-go/antlr/v4 v4.13.1 // indirect
	github.com/docker/cli v29.8.2+incompatible // indirect
	github.com/docker/docker-credential-helpers v0.9.9 // indirect
	github.com/google/go-containerregistry v0.22.1 // indirect
	github.com/klauspost/compress v1.20.1 // indirect
	github.com/opencontainers/go-digest v1.0.0 // indirect
	github.com/opencontainers/image-spec v1.1.1 // indirect
	github.com/sirupsen/logrus v1.10.2 // indirect
	golang.org/x/exp v0.0.0-20260908205506-85c1c2202aba // indirect
	golang.org/x/sys v0.48.0 // indirect
	golang.org/x/text v0.42.0 // indirect
	google.golang.org/genproto/googleapis/api v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc // indirect
	google.golang.org/protobuf v1.36.12 // indirect
)
