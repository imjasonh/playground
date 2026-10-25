//go:build cgo

package host

// cgoEnabled reports whether this binary was built with cgo.
// plugin.Open is implemented only in cgo builds.
const cgoEnabled = true
