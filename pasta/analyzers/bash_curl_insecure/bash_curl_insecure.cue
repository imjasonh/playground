// bash_curl_insecure flags `curl -k` / `curl --insecure`. Disabling
// TLS verification defeats the point of HTTPS and is almost never
// appropriate outside a short-lived local debug session. No auto-fix.

package bash_curl_insecure

import (
	"github.com/imjasonh/pasta/schema"
	bashlang "github.com/imjasonh/pasta/lang/bash"
)

bash_curl_insecure: schema.#Analyzer & {
	name:    "bash_curl_insecure"
	version: "0.1.0"
	doc:     "Flag curl -k / --insecure"
	facts: {}

	rules: curl_insecure: {
		name:      "curl_insecure"
		doc:       "Flag TLS verification bypass on curl"
		languages: [bashlang.Name]
		requires: []
		provides: []

		match: {
			node: "command"
			where: [{op: "matches", args: ["@_root", "(?s)^curl\\b.*(\\s-k\\b|\\s--insecure\\b)"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "curl -k/--insecure disables TLS verification"
		}
	}
}
