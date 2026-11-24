// terraform_github_oidc flags cloud trust policies that let more GitHub
// Actions workflows exchange their OIDC token for cloud credentials
// than the author meant.
//
// GitHub mints every Actions OIDC token from one issuer,
// https://token.actions.githubusercontent.com, so a trust policy that
// names the issuer and nothing else trusts every workflow in every
// repository on github.com. Owner and repository names are also not
// stable: when an owner renames or deletes a repository or account,
// anyone can register the freed name and inherit the trust. Pin the
// numeric repository_id and repository_owner_id claims instead.
//
// The rules read literal text inside one resource or data block, like
// terraform_security. They don't evaluate variables or locals. When a
// GCP attribute_condition is built from a reference, such as
// local.github_repository_condition, the rules that need to see the
// whole condition stay quiet rather than guess.

package terraform_github_oidc

import (
	"github.com/imjasonh/pasta/schema"
	hcllang "github.com/imjasonh/pasta/lang/hcl"
	tflang "github.com/imjasonh/pasta/lang/terraform"
)

_langs: [hcllang.Name, tflang.Name]

_githubIssuer: #"token\.actions\.githubusercontent\.com"#

// A claim in an attribute_condition is followed by an operator or a
// method call, or preceded by an operator. In attribute_mapping it is a
// whole quoted string ("assertion.sub"), which neither form matches.
_claim: {
	_names: string
	out:    #"(?:(?:==|!=|&&|\|\||\(|\[|,|!)\s*(?:"# + _names + #")\b|(?:"# + _names + #")\b[^"])"#
}

_nameClaim: (_claim & {
	_names: #"assertion\.(?:sub|repository|repository_owner)|attribute\.(?:repository|repository_owner)|google\.subject"#
}).out

_idClaim: (_claim & {
	_names: #"(?:assertion|attribute)\.repository(?:_owner)?_id"#
}).out

_anyRepositoryClaim: (_claim & {
	_names: #"assertion\.(?:sub|repository(?:_owner)?(?:_id)?)|attribute\.repository(?:_owner)?(?:_id)?|google\.subject"#
}).out

_hasCondition:     #"(?m)^\s*attribute_condition\s*="#
_trivialCondition: #"(?m)^\s*attribute_condition\s*=\s*"\s*(?:true)?\s*"\s*$"#

// _blockRule flags a resource or data block whose kind matches _kinds,
// whose first label matches _types (quotes included), and whose text
// satisfies every predicate in _where.
_blockRule: {
	_kinds: string
	_types: string
	_where: [...schema.#Predicate]
	_message:  string
	_severity: schema.#Severity
	_name:     string
	_doc:      string

	out: {
		name:      _name
		doc:       _doc
		languages: _langs
		requires: []
		provides: []

		match: {
			node: "block"
			children: [
				{capture: "kind", pattern: {node: "identifier"}},
				{capture: "type", pattern: {node: "string_lit"}},
			]
			where: [
				{op: "matches", args: ["@kind", _kinds]},
				{op: "matches", args: ["@type", _types]},
				for p in _where {p},
			]
		}

		diagnose: {
			severity: _severity
			message:  _message
		}
	}
}

_gcpProvider: _blockRule & {
	_kinds: "^resource$"
	_types: #"^"google_iam_workload_identity_pool_provider"$"#
}

_gcpMember: _blockRule & {
	_kinds: "^(resource|data)$"
	_types: #"^"google_[a-z0-9_]+"$"#
}

_awsTrust: _blockRule & {
	_kinds: "^(resource|data)$"
	_types: #"^"(aws_iam_role|aws_iam_policy_document)"$"#
}

terraform_github_oidc: schema.#Analyzer & {
	name:    "terraform_github_oidc"
	version: "0.1.0"
	doc:     "GCP Workload Identity and AWS IAM trust policies that accept GitHub Actions OIDC tokens from too many repositories, or match a repository by name instead of by ID"
	facts: {}

	rules: {
		// --- GCP Workload Identity pool providers -------------------------
		gcp_github_provider_no_condition: (_gcpProvider & {
			_where: [
				{op: "matches", args: ["@_root", _githubIssuer]},
				{op: "not_matches", args: ["@_root", _hasCondition]},
			]
			_message:  "Workload Identity provider trusts GitHub's OIDC issuer with no attribute_condition, so any GitHub repository can federate into the pool; pin assertion.repository_id and assertion.repository_owner_id"
			_severity: "error"
			_name:     "gcp_github_provider_no_condition"
			_doc:      "Flag GitHub Workload Identity pool providers without an attribute_condition"
		}).out

		gcp_github_provider_trivial_condition: (_gcpProvider & {
			_where: [
				{op: "matches", args: ["@_root", _githubIssuer]},
				{op: "matches", args: ["@_root", _trivialCondition]},
			]
			_message:  "Workload Identity provider's attribute_condition is empty or always true, so any GitHub repository can federate into the pool; pin assertion.repository_id and assertion.repository_owner_id"
			_severity: "error"
			_name:     "gcp_github_provider_trivial_condition"
			_doc:      "Flag GitHub Workload Identity pool providers whose attribute_condition is \"\" or \"true\""
		}).out

		gcp_github_provider_any_repository: (_gcpProvider & {
			_where: [
				{op: "matches", args: ["@_root", _githubIssuer]},
				{op: "matches", args: ["@_root", _hasCondition]},
				{op: "not_matches", args: ["@_root", _trivialCondition]},
				{op: "not_matches", args: ["@_root", _anyRepositoryClaim]},
				// A reference can hide the repository check, so stay quiet
				// on one.
				{op: "not_matches", args: ["@_root", #"(?s)attribute_condition\s*=.*\b(?:var|local|module|data)\.\w"#]},
			]
			_message:  "Workload Identity provider's attribute_condition never checks the repository or owner, so a workflow in any GitHub repository that meets it can federate into the pool; pin assertion.repository_id and assertion.repository_owner_id"
			_severity: "error"
			_name:     "gcp_github_provider_any_repository"
			_doc:      "Flag GitHub Workload Identity pool providers whose attribute_condition doesn't restrict the repository or owner"
		}).out

		gcp_github_provider_name_only: (_gcpProvider & {
			_where: [
				{op: "matches", args: ["@_root", _githubIssuer]},
				{op: "matches", args: ["@_root", _nameClaim]},
				{op: "not_matches", args: ["@_root", _idClaim]},
			]
			_message:  "Workload Identity provider matches the GitHub repository or owner by name; a renamed or deleted name can be registered by anyone, so also match assertion.repository_id and assertion.repository_owner_id"
			_severity: "error"
			_name:     "gcp_github_provider_name_only"
			_doc:      "Flag GitHub Workload Identity pool providers that check repository, repository_owner, or sub without a numeric ID claim"
		}).out

		// --- GCP IAM members on a Workload Identity pool -----------------
		gcp_workload_identity_pool_wildcard_member: (_gcpMember & {
			_where: [
				{op: "matches", args: ["@_root", #"principalSet://iam\.googleapis\.com/[^"]*/\*""#]},
			]
			_message:  "IAM member principalSet://.../* grants every identity in the Workload Identity pool; bind a specific attribute such as attribute.repository_id instead"
			_severity: "error"
			_name:     "gcp_workload_identity_pool_wildcard_member"
			_doc:      "Flag IAM members that grant a whole Workload Identity pool with principalSet://.../*"
		}).out

		gcp_workload_identity_member_by_name: (_gcpMember & {
			_where: [
				{op: "matches", args: ["@_root", #"principalSet://iam\.googleapis\.com/[^"]*/attribute\.repository(?:_owner)?/|principal://iam\.googleapis\.com/[^"]*/subject/repo:"#]},
			]
			_message:  "IAM member binds a GitHub repository or owner by name; a renamed or deleted name can be registered by anyone, so map assertion.repository_id and bind attribute.repository_id instead"
			_severity: "error"
			_name:     "gcp_workload_identity_member_by_name"
			_doc:      "Flag Workload Identity IAM members on attribute.repository, attribute.repository_owner, or a repo: subject"
		}).out

		// --- AWS IAM role trust policies ---------------------------------
		aws_github_oidc_no_sub: (_awsTrust & {
			_where: [
				{op: "matches", args: ["@_root", _githubIssuer]},
				{op: "matches", args: ["@_root", "AssumeRoleWithWebIdentity"]},
				{op: "not_matches", args: ["@_root", _githubIssuer + #":sub\b"#]},
			]
			_message:  "IAM trust policy lets GitHub's OIDC provider assume the role without a token.actions.githubusercontent.com:sub condition, so any GitHub repository can assume it"
			_severity: "error"
			_name:     "aws_github_oidc_no_sub"
			_doc:      "Flag AssumeRoleWithWebIdentity trust policies for GitHub without a sub condition"
		}).out

		aws_github_oidc_wildcard_owner: (_awsTrust & {
			_where: [
				{op: "matches", args: ["@_root", _githubIssuer + #":sub\b"#]},
				{op: "matches", args: ["@_root", #""repo:[^/"]*\*|githubusercontent\.com:sub"\s*(?:[:=]|values\s*=)\s*\[?\s*"\*"|values\s*=\s*\[\s*"\*"\s*\]\s*variable\s*=\s*"token\.actions\.githubusercontent\.com:sub""#]},
			]
			_message:  "IAM trust policy's token.actions.githubusercontent.com:sub condition has a wildcard in the owner, so repositories under other GitHub accounts can assume the role; name the owner, as in repo:OWNER/REPO:*"
			_severity: "error"
			_name:     "aws_github_oidc_wildcard_owner"
			_doc:      "Flag GitHub trust policies whose sub matches \"*\" or puts a wildcard in the repo: owner"
		}).out
	}
}
