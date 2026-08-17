// gha_security ports the high-signal offline checks from tools like
// zizmor (https://docs.zizmor.sh/audits/) onto GitHub Actions workflow /
// composite-action / Dependabot YAML via tree-sitter patterns.
//
// Online-only zizmor audits (impostor-commit, known-vulnerable-actions,
// archived-uses, ref-confusion, stale-action-refs, typosquat live check)
// are intentionally out of scope — pasta has no network side channel.
// Semantic cache-poisoning / ref-version-mismatch / unsound-* expression
// analysis is similarly deferred; what remains is structural YAML that
// pattern-matches cleanly.
//
// Rules gate on GHA-shaped content (uses:/jobs:/runs-on:/package-ecosystem)
// so ordinary application YAML is left alone. Playground CI disables the
// noisiest findings against this repo's still-tag-pinned workflows via
// .pasta/pasta.cue.

package gha_security

import (
	"github.com/imjasonh/pasta/schema"
	yamllang "github.com/imjasonh/pasta/lang/yaml"
)

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

// _keyValuePair matches `key: <scalar-or-block value>` and runs a regex on
// the value text. Key compared via eq on the plain_scalar under flow_node.
_keyValuePair: {
	_key:     string
	_regex:   string
	_message: string
	_severity: schema.#Severity | *"warning"
	_name:    string
	_doc:     string

	out: {
		name:      _name
		doc:       _doc
		languages: [yamllang.Name]
		requires: []
		provides: []

		match: {
			node: "block_mapping_pair"
			fields: {
				key: {
					node: "flow_node"
					children: [{
						capture: "k"
						pattern: {node: "plain_scalar"}
					}]
				}
				value: {
					capture: "v"
					pattern: {node: ["flow_node", "block_node"]}
				}
			}
			where: [
				{op: "eq", args: ["@k", _key]},
				{op: "matches", args: ["@v", _regex]},
			]
		}

		diagnose: {
			severity: _severity
			message:  _message
		}
	}
}

// _keyOnly flags a mapping key regardless of whether it has a value
// (covers `pull_request_target:` empty trigger forms).
_keyOnly: {
	_key:      string
	_message:  string
	_severity: schema.#Severity | *"warning"
	_name:     string
	_doc:      string

	out: {
		name:      _name
		doc:       _doc
		languages: [yamllang.Name]
		requires: []
		provides: []

		match: {
			node: "block_mapping_pair"
			fields: key: {
				node: "flow_node"
				children: [{
					capture: "k"
					pattern: {node: "plain_scalar"}
				}]
			}
			where: [{op: "eq", args: ["@k", _key]}]
		}

		diagnose: {
			severity: _severity
			message:  _message
		}
	}
}

// ---------------------------------------------------------------------------
// Analyzer
// ---------------------------------------------------------------------------

gha_security: schema.#Analyzer & {
	name:    "gha_security"
	version: "0.1.0"
	doc:     "GitHub Actions / Dependabot security checks (zizmor-inspired, offline)"
	facts: {}

	rules: {
		// --- unpinned-uses -------------------------------------------------
		// RE2 has no lookahead, so pin-check is matches(owner/repo@ref) +
		// not_matches(@40-char-sha).
		unpinned_uses: {
			name:      "unpinned_uses"
			doc:       "Flag owner/repo@tag|branch uses: (require hash pin)"
			languages: [yamllang.Name]
			requires: []
			provides: []

			match: {
				node: "block_mapping_pair"
				fields: {
					key: {
						node: "flow_node"
						children: [{
							capture: "k"
							pattern: {node: "plain_scalar"}
						}]
					}
					value: {
						capture: "v"
						pattern: {node: ["flow_node", "block_node"]}
					}
				}
				where: [
					{op: "eq", args: ["@k", "uses"]},
					{op: "matches", args: ["@v", "^[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9_./-]+@.+$"]},
					{op: "not_matches", args: ["@v", "^[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9_./-]+@[0-9a-fA-F]{40}$"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "unpinned actions ref; pin uses: to a full commit SHA (zizmor unpinned-uses)"
			}
		}

		// --- dangerous-triggers --------------------------------------------
		dangerous_trigger_pull_request_target: (_keyOnly & {
			_key:      "pull_request_target"
			_message:  "dangerous trigger pull_request_target runs in the base repo context (zizmor dangerous-triggers)"
			_severity: "error"
			_name:     "dangerous_trigger_pull_request_target"
			_doc:      "Flag pull_request_target trigger keys"
		}).out

		dangerous_trigger_workflow_run: (_keyOnly & {
			_key:      "workflow_run"
			_message:  "dangerous trigger workflow_run runs in the base repo context (zizmor dangerous-triggers)"
			_severity: "error"
			_name:     "dangerous_trigger_workflow_run"
			_doc:      "Flag workflow_run trigger keys"
		}).out

		dangerous_trigger_on_scalar: (_keyValuePair & {
			_key:      "on"
			_regex:    "^(pull_request_target|workflow_run)$"
			_message:  "dangerous workflow trigger (zizmor dangerous-triggers)"
			_severity: "error"
			_name:     "dangerous_trigger_on_scalar"
			_doc:      "Flag on: pull_request_target|workflow_run scalar form"
		}).out

		// --- excessive-permissions ----------------------------------------
		permissions_write_all: (_keyValuePair & {
			_key:      "permissions"
			_regex:    "^write-all$"
			_message:  "permissions: write-all grants every scope; prefer minimal job-level permissions (zizmor excessive-permissions)"
			_severity: "error"
			_name:     "permissions_write_all"
			_doc:      "Flag permissions: write-all"
		}).out

		permissions_read_all: (_keyValuePair & {
			_key:      "permissions"
			_regex:    "^read-all$"
			_message:  "permissions: read-all is overly broad; prefer minimal job-level permissions (zizmor excessive-permissions)"
			_severity: "warning"
			_name:     "permissions_read_all"
			_doc:      "Flag permissions: read-all"
		}).out

		// --- self-hosted-runner --------------------------------------------
		self_hosted_runner_scalar: (_keyValuePair & {
			_key:      "runs-on"
			_regex:    "^self-hosted$"
			_message:  "self-hosted runner; ensure the runner is hardened and not exposed to untrusted workflows (zizmor self-hosted-runner)"
			_severity: "warning"
			_name:     "self_hosted_runner_scalar"
			_doc:      "Flag runs-on: self-hosted"
		}).out

		self_hosted_runner_label: {
			name:      "self_hosted_runner_label"
			doc:       "Flag self-hosted label inside runs-on sequences"
			languages: [yamllang.Name]
			requires: []
			provides: []
			require_substring: ["self-hosted"]

			match: {
				node: "plain_scalar"
				where: [
					{op: "eq", args: ["@_root", "self-hosted"]},
					{op: "ancestor_is", args: ["@_root", "flow_sequence"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "self-hosted runner label; ensure the runner is hardened (zizmor self-hosted-runner)"
			}
		}

		// --- secrets-inherit -----------------------------------------------
		secrets_inherit: (_keyValuePair & {
			_key:      "secrets"
			_regex:    "^inherit$"
			_message:  "secrets: inherit forwards all caller secrets to a reusable workflow (zizmor secrets-inherit)"
			_severity: "warning"
			_name:     "secrets_inherit"
			_doc:      "Flag secrets: inherit"
		}).out

		// --- insecure-commands ---------------------------------------------
		insecure_commands: (_keyOnly & {
			_key:      "ACTIONS_ALLOW_UNSECURE_COMMANDS"
			_message:  "ACTIONS_ALLOW_UNSECURE_COMMANDS re-enables deprecated set-env/add-path commands (zizmor insecure-commands)"
			_severity: "error"
			_name:     "insecure_commands"
			_doc:      "Flag ACTIONS_ALLOW_UNSECURE_COMMANDS"
		}).out

		// --- artipacked ----------------------------------------------------
		// Step-level: uses actions/checkout without persist-credentials: false.
		artipacked: {
			name:      "artipacked"
			doc:       "Flag actions/checkout without persist-credentials: false"
			languages: [yamllang.Name]
			requires: []
			provides: []
			require_substring: ["actions/checkout"]

			match: {
				node: "block_sequence_item"
				where: [
					{op: "matches", args: ["@_root", "(?s)uses:\\s*actions/checkout@"]},
					{op: "not_matches", args: ["@_root", "persist-credentials:\\s*false"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "actions/checkout persists git credentials by default; set with.persist-credentials to false (zizmor artipacked)"
			}
		}

		// --- template-injection --------------------------------------------
		template_injection: (_keyValuePair & {
			_key:      "run"
			_regex: "(?s)\\$\\{\\{\\s*(github\\.event\\.(issue|comment|discussion|review|review_comment)\\.(title|body)|github\\.event\\.pull_request\\.(title|body|head\\.(ref|label))|github\\.event\\.head_commit\\.(message|author\\.(email|name))|github\\.event\\.commits\\.[^\\s}]+\\.author\\.(email|name)|github\\.head_ref|github\\.event\\.pages\\.[^\\s}]+\\.page_name)\\s*\\}\\}"
			_message: "template expansion of attacker-controllable context in run:; pass via env: instead (zizmor template-injection)"
			_severity: "error"
			_name: "template_injection"
			_doc:  "Flag dangerous ${{ github.event.* }} expansions inside run:"
		}).out

		// --- secrets-outside-env -------------------------------------------
		secrets_in_run: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)\\$\\{\\{\\s*secrets\\."
			_message:  "secret expanded directly in run:; prefer env: mapping then shell expansion (zizmor secrets-outside-env)"
			_severity: "warning"
			_name:     "secrets_in_run"
			_doc:      "Flag ${{ secrets.* }} inside run: scripts"
		}).out

		// --- bot-conditions ------------------------------------------------
		bot_conditions: (_keyValuePair & {
			_key:      "if"
			_regex:    "github\\.actor\\s*=="
			_message:  "github.actor bot check is spoofable; prefer github.event.pull_request.user.login (zizmor bot-conditions)"
			_severity: "warning"
			_name:     "bot_conditions"
			_doc:      "Flag spoofable github.actor conditions"
		}).out

		// --- adhoc-packages ------------------------------------------------
		adhoc_npm_install: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)(^|[\\n;&|]|\\s)npm\\s+install\\b"
			_message:  "ad-hoc npm install in CI; prefer npm ci from a committed lockfile (zizmor adhoc-packages)"
			_severity: "warning"
			_name:     "adhoc_npm_install"
			_doc:      "Flag npm install in run: steps"
		}).out

		adhoc_yarn_add: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)(^|[\\n;&|]|\\s)yarn\\s+add\\b"
			_message:  "ad-hoc yarn add mutates lockfile state in CI (zizmor adhoc-packages)"
			_severity: "warning"
			_name:     "adhoc_yarn_add"
			_doc:      "Flag yarn add in run: steps"
		}).out

		adhoc_pnpm_add: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)(^|[\\n;&|]|\\s)pnpm\\s+add\\b"
			_message:  "ad-hoc pnpm add mutates lockfile state in CI (zizmor adhoc-packages)"
			_severity: "warning"
			_name:     "adhoc_pnpm_add"
			_doc:      "Flag pnpm add in run: steps"
		}).out

		adhoc_gem_install: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)(^|[\\n;&|]|\\s)gem\\s+install\\b"
			_message:  "ad-hoc gem install in CI; prefer bundle install from a Gemfile.lock (zizmor adhoc-packages)"
			_severity: "warning"
			_name:     "adhoc_gem_install"
			_doc:      "Flag gem install in run: steps"
		}).out

		adhoc_bundle_add: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)(^|[\\n;&|]|\\s)bundle\\s+add\\b"
			_message:  "ad-hoc bundle add mutates Gemfile.lock in CI (zizmor adhoc-packages)"
			_severity: "warning"
			_name:     "adhoc_bundle_add"
			_doc:      "Flag bundle add in run: steps"
		}).out

		// --- unpinned-images / docker uses ---------------------------------
		unpinned_docker_uses: {
			name:      "unpinned_docker_uses"
			doc:       "Flag docker://image:tag without @sha256 digest"
			languages: [yamllang.Name]
			requires: []
			provides: []

			match: {
				node: "block_mapping_pair"
				fields: {
					key: {
						node: "flow_node"
						children: [{
							capture: "k"
							pattern: {node: "plain_scalar"}
						}]
					}
					value: {
						capture: "v"
						pattern: {node: ["flow_node", "block_node"]}
					}
				}
				where: [
					{op: "eq", args: ["@k", "uses"]},
					{op: "matches", args: ["@v", "^docker://.+"]},
					{op: "not_matches", args: ["@v", "@sha256:[0-9a-fA-F]+"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "docker:// action image is not digest-pinned (zizmor unpinned-images)"
			}
		}

		unpinned_container_image: {
			name:      "unpinned_container_image"
			doc:       "Flag container.image: without @sha256 digest"
			languages: [yamllang.Name]
			requires: []
			provides: []

			match: {
				node: "block_mapping_pair"
				fields: {
					key: {
						node: "flow_node"
						children: [{
							capture: "k"
							pattern: {node: "plain_scalar"}
						}]
					}
					value: {
						capture: "v"
						pattern: {node: ["flow_node", "block_node"]}
					}
				}
				where: [
					{op: "eq", args: ["@k", "image"]},
					{op: "matches", args: ["@v", ":" ]},
					{op: "not_matches", args: ["@v", "@sha256:"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "container image is tag-pinned, not digest-pinned (zizmor unpinned-images)"
			}
		}

		// --- hardcoded-container-credentials -------------------------------
		hardcoded_container_credentials: {
			name:      "hardcoded_container_credentials"
			doc:       "Flag container.credentials: mappings that set a password"
			languages: [yamllang.Name]
			requires: []
			provides: []
			require_substring: ["credentials:", "password:"]

			match: {
				node: "block_mapping_pair"
				fields: {
					key: {
						node: "flow_node"
						children: [{
							capture: "k"
							pattern: {node: "plain_scalar"}
						}]
					}
					value: {
						capture: "v"
						pattern: {node: "block_node"}
					}
				}
				where: [
					{op: "eq", args: ["@k", "credentials"]},
					{op: "matches", args: ["@v", "(?s)(^|\\n)\\s*password:"]},
				]
			}

			diagnose: {
				severity: "error"
				message:  "container registry credentials with password: in workflow YAML (zizmor hardcoded-container-credentials)"
			}
		}

		// --- insecure-url-scheme -------------------------------------------
		insecure_http_url: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)\\bhttp://[^\\s\"']+"
			_message:  "insecure http:// URL in run: script (zizmor insecure-url-scheme)"
			_severity: "warning"
			_name:     "insecure_http_url"
			_doc:      "Flag http:// URLs inside run: scripts"
		}).out

		// --- anonymous-definition ------------------------------------------
		anonymous_workflow: {
			name:      "anonymous_workflow"
			doc:       "Flag workflows missing a top-level name: field"
			languages: [yamllang.Name]
			requires: []
			provides: []
			require_substring: ["jobs:"]

			match: {
				node: "document"
				where: [
					{op: "matches", args: ["@_root", "(?m)^jobs:"]},
					{op: "not_matches", args: ["@_root", "(?m)^name\\s*:"]},
				]
			}

			diagnose: {
				severity: "hint"
				message:  "workflow has no top-level name: (zizmor anonymous-definition)"
			}
		}

		// --- github-env ----------------------------------------------------
		github_env_write: (_keyValuePair & {
			_key:      "run"
			_regex:    "(?s)(>>|tee\\s+-a)\\s*(\\\")?\\$GITHUB_ENV"
			_message:  "writing to GITHUB_ENV can enable environment injection; avoid untrusted data (zizmor github-env)"
			_severity: "warning"
			_name:     "github_env_write"
			_doc:      "Flag redirects into $GITHUB_ENV in run: scripts"
		}).out

		// --- overprovisioned-secrets ---------------------------------------
		overprovisioned_secrets: (_keyValuePair & {
			_key:      "secrets"
			_regex:    "^['\"]?\\*['\"]?$"
			_message:  "secrets: '*' forwards every secret; pass an explicit allowlist (zizmor overprovisioned-secrets)"
			_severity: "warning"
			_name:     "overprovisioned_secrets"
			_doc:      "Flag secrets: '*' "
		}).out

		// --- superfluous-actions -------------------------------------------
		superfluous_actions: (_keyValuePair & {
			_key: "uses"
			_regex: "^(ncipollo/release-action|softprops/action-gh-release|elgohr/Github-Release-Action|peter-evans/create-pull-request|peter-evans/create-or-update-comment|dacbd/create-issue-action|actions-ecosystem/action-add-labels|actions-ecosystem/action-remove-labels|svenstaro/upload-release-action|addnab/docker-run-action|sergeysova/jq-action|dtolnay/rust-toolchain|stefanzweifel/git-auto-commit-action|EndBug/add-and-commit)@"
			_message: "superfluous action; prefer preinstalled runner tools / gh CLI (zizmor superfluous-actions)"
			_severity: "info"
			_name: "superfluous_actions"
			_doc:  "Flag common actions replaceable by gh/rustup/docker/jq"
		}).out

		// --- github-app ----------------------------------------------------
		github_app_skip_revoke: {
			name:      "github_app_skip_revoke"
			doc:       "Flag skip-token-revoke: true on create-github-app-token"
			languages: [yamllang.Name]
			requires: []
			provides: []
			require_substring: ["skip-token-revoke"]

			match: {
				node: "block_sequence_item"
				where: [
					{op: "matches", args: ["@_root", "(?s)uses:\\s*actions/create-github-app-token@"]},
					{op: "matches", args: ["@_root", "skip-token-revoke:\\s*true"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "skip-token-revoke: true leaves GitHub App tokens valid after the job (zizmor github-app)"
			}
		}

		// --- dependabot-cooldown -------------------------------------------
		dependabot_missing_cooldown: {
			name:      "dependabot_missing_cooldown"
			doc:       "Flag Dependabot configs without a cooldown: block"
			languages: [yamllang.Name]
			requires: []
			provides: []
			file_match: ["dependabot.yml", "dependabot.yaml"]
			require_substring: ["package-ecosystem"]

			match: {
				node: "document"
				where: [{op: "not_matches", args: ["@_root", "(?m)^\\s*cooldown:"]}]
			}

			diagnose: {
				severity: "warning"
				message:  "Dependabot config lacks cooldown:; prefer at least 7 days (zizmor dependabot-cooldown)"
			}
		}

		// --- dependabot-execution ------------------------------------------
		dependabot_allow_code_exec: (_keyValuePair & {
			_key:      "insecure-external-code-execution"
			_regex:    "^allow$"
			_message:  "Dependabot insecure-external-code-execution: allow (zizmor dependabot-execution)"
			_severity: "warning"
			_name:     "dependabot_allow_code_exec"
			_doc:      "Flag insecure-external-code-execution: allow"
		}).out & {
			file_match: ["dependabot.yml", "dependabot.yaml"]
		}

		// --- concurrency-limits (pedantic) ---------------------------------
		missing_concurrency: {
			name:      "missing_concurrency"
			doc:       "Flag workflows without a concurrency: block"
			languages: [yamllang.Name]
			requires: []
			provides: []
			require_substring: ["jobs:"]

			match: {
				node: "document"
				where: [
					{op: "matches", args: ["@_root", "(?m)^jobs:"]},
					{op: "not_matches", args: ["@_root", "(?m)^concurrency:"]},
				]
			}

			diagnose: {
				severity: "hint"
				message:  "workflow has no concurrency: limit (zizmor concurrency-limits)"
			}
		}
	}
}
