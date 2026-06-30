module github.com/imjasonh/playground/ocidb

go 1.25.0

require (
	github.com/google/go-containerregistry v0.20.6
	github.com/klauspost/compress v1.18.0
	github.com/values-conflict/go-sqlite-fdw v0.0.0
	github.com/values-conflict/go-sqlite-fdw/modernc v0.0.0-20260630071241-65cea68abcec
	modernc.org/sqlite v1.53.0
)

require (
	github.com/containerd/stargz-snapshotter/estargz v0.16.3 // indirect
	github.com/docker/cli v28.2.2+incompatible // indirect
	github.com/docker/distribution v2.8.3+incompatible // indirect
	github.com/docker/docker-credential-helpers v0.9.3 // indirect
	github.com/dustin/go-humanize v1.0.1 // indirect
	github.com/google/uuid v1.6.0 // indirect
	github.com/mattn/go-isatty v0.0.20 // indirect
	github.com/mitchellh/go-homedir v1.1.0 // indirect
	github.com/ncruces/go-strftime v1.0.0 // indirect
	github.com/opencontainers/go-digest v1.0.0 // indirect
	github.com/opencontainers/image-spec v1.1.1 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	github.com/remyoudompheng/bigfft v0.0.0-20230129092748-24d4a6f8daec // indirect
	github.com/sirupsen/logrus v1.9.3 // indirect
	github.com/vbatts/tar-split v0.12.1 // indirect
	golang.org/x/sync v0.21.0 // indirect
	golang.org/x/sys v0.46.0 // indirect
	modernc.org/libc v1.73.4 // indirect
	modernc.org/mathutil v1.7.1 // indirect
	modernc.org/memory v1.11.0 // indirect
)

// The published modernc backend pins the core module to a bare v0.0.0 and
// relies on a local `replace => ../` that only works inside its own repo.
// Redirect that to the real tagged commit so external consumers can build.
replace github.com/values-conflict/go-sqlite-fdw => github.com/values-conflict/go-sqlite-fdw v0.0.0-20260630071241-65cea68abcec
