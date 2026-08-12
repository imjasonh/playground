//go:build race

package e2e_test

// Under -race, keep smoke tests serial to avoid amplifying race-detector
// overhead on the shared wazero runtime init path.
const parallelSmoke = false
