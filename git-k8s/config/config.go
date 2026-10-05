// Package config holds the YAML that git-k8s programs install themselves.
package config

import _ "embed"

// Policy is policy.yaml, which holds the admission policies, their bindings,
// and the ConfigMap that some of the policies read. The core program
// installs it when it starts.
//
//go:embed policy.yaml
var Policy []byte
