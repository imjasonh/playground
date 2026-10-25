//go:build race

package host

// raceEnabled reports whether this binary was built with -race.
// A plugin's runtime package must be compiled with the same flag.
const raceEnabled = true
