// wrangler_observability requires every Cloudflare Worker wrangler.toml
// to keep Workers Logs (including invocation logs) and Workers Traces
// enabled. Playground defaults to 100% head sampling; dial the rates
// down before serious volume, but do not turn the blocks off.

package wrangler_observability

import (
	"github.com/imjasonh/pasta/schema"
	tomllang "github.com/imjasonh/pasta/lang/toml"
)

_wranglerFile: ["wrangler.toml"]

wrangler_observability: schema.#Analyzer & {
	name:    "wrangler_observability"
	version: "0.1.0"
	doc:     "Require Workers Logs and Traces in every wrangler.toml"
	facts: {}

	rules: {
		missing_observability: {
			name:      "missing_observability"
			doc:       "Flag wrangler.toml without [observability] enabled = true"
			languages: [tomllang.Name]
			requires: []
			provides: []
			file_match: _wranglerFile

			match: {
				node: "document"
				where: [{
					op: "not_matches"
					args: ["@_root", "(?ms)^\\[observability\\][^\\[]*\\benabled\\s*=\\s*true"]
				}]
			}

			diagnose: {
				severity: "error"
				message:  "wrangler.toml must enable [observability] (enabled = true)"
			}
		}

		missing_observability_logs: {
			name:      "missing_observability_logs"
			doc:       "Flag wrangler.toml without [observability.logs] enabled = true"
			languages: [tomllang.Name]
			requires: []
			provides: []
			file_match: _wranglerFile

			match: {
				node: "document"
				where: [{
					op: "not_matches"
					args: ["@_root", "(?ms)^\\[observability\\.logs\\][^\\[]*\\benabled\\s*=\\s*true"]
				}]
			}

			diagnose: {
				severity: "error"
				message:  "wrangler.toml must enable [observability.logs] (enabled = true)"
			}
		}

		missing_invocation_logs: {
			name:      "missing_invocation_logs"
			doc:       "Flag wrangler.toml without invocation_logs = true under [observability.logs]"
			languages: [tomllang.Name]
			requires: []
			provides: []
			file_match: _wranglerFile

			match: {
				node: "document"
				where: [{
					op: "not_matches"
					args: ["@_root", "(?ms)^\\[observability\\.logs\\][^\\[]*\\binvocation_logs\\s*=\\s*true"]
				}]
			}

			diagnose: {
				severity: "error"
				message:  "wrangler.toml must set invocation_logs = true under [observability.logs]"
			}
		}

		missing_observability_traces: {
			name:      "missing_observability_traces"
			doc:       "Flag wrangler.toml without [observability.traces] enabled = true"
			languages: [tomllang.Name]
			requires: []
			provides: []
			file_match: _wranglerFile

			match: {
				node: "document"
				where: [{
					op: "not_matches"
					args: ["@_root", "(?ms)^\\[observability\\.traces\\][^\\[]*\\benabled\\s*=\\s*true"]
				}]
			}

			diagnose: {
				severity: "error"
				message:  "wrangler.toml must enable [observability.traces] (enabled = true)"
			}
		}
	}
}
