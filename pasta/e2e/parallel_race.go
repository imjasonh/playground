//go:build race

package e2e_test

// Under -race, gotreesitter's process-global arenas are not safe to
// share across parallel RunGroup calls, so e2e subtests stay serial.
const parallelSmoke = false
