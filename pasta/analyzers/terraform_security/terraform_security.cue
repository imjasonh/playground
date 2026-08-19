// terraform_security ports high-signal offline checks from
// Checkov (https://github.com/bridgecrewio/checkov) onto Terraform and
// OpenTofu HCL via tree-sitter patterns.
//
// Graph checks (CKV2_*), variable/module expansion, Terraform plan
// JSON, and registry lookups are out of scope — pasta has no evaluator
// and no network side channel. What remains is structural HCL that
// pattern-matches cleanly: literal attributes on resource, data,
// module, and provider blocks.

package terraform_security

import (
	"github.com/imjasonh/pasta/schema"
	hcllang "github.com/imjasonh/pasta/lang/hcl"
	tflang "github.com/imjasonh/pasta/lang/terraform"
)

_langs: [hcllang.Name, tflang.Name]

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

// _resourceMatches flags a `resource "TYPE" "name"` block whose text
// matches _regex. _types is a regex matched against the type
// string_lit (quotes included), so quote each type for an exact match.
_resourceMatches: {
	_types:    string
	_regex:    string
	_message:  string
	_severity: schema.#Severity | *"warning"
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
				{op: "eq", args: ["@kind", "resource"]},
				{op: "matches", args: ["@type", _types]},
				{op: "matches", args: ["@_root", _regex]},
			]
		}

		diagnose: {
			severity: _severity
			message:  _message
		}
	}
}

// _resourceLacks flags a resource block whose text does not match
// _regex (typically a required hardening attribute).
_resourceLacks: {
	_types:    string
	_regex:    string
	_message:  string
	_severity: schema.#Severity | *"warning"
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
				{op: "eq", args: ["@kind", "resource"]},
				{op: "matches", args: ["@type", _types]},
				{op: "not_matches", args: ["@_root", _regex]},
			]
		}

		diagnose: {
			severity: _severity
			message:  _message
		}
	}
}

// _kindMatches flags any block whose first identifier is _kind and
// whose text matches _regex (module, provider, nested ingress, …).
_kindMatches: {
	_kind:     string
	_regex:    string
	_message:  string
	_severity: schema.#Severity | *"warning"
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
			children: [{
				capture: "kind"
				pattern: {node: "identifier"}
			}]
			where: [
				{op: "eq", args: ["@kind", _kind]},
				{op: "matches", args: ["@_root", _regex]},
			]
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

terraform_security: schema.#Analyzer & {
	name:    "terraform_security"
	version: "0.1.0"
	doc:     "Terraform / OpenTofu security checks (Checkov-inspired, offline)"
	facts: {}

	rules: {
		// --- modules -------------------------------------------------------
		unpinned_module_source: {
			name:      "unpinned_module_source"
			doc:       "Flag remote module sources that are not pinned to a 40-char git commit"
			languages: _langs
			requires: []
			provides: []

			match: {
				node: "block"
				children: [{
					capture: "kind"
					pattern: {node: "identifier"}
				}]
				where: [
					{op: "eq", args: ["@kind", "module"]},
					{op: "matches", args: ["@_root", "source\\s*="]},
					{op: "not_matches", args: ["@_root", "source\\s*=\\s*\"(\\.|/|\\.\\./)"]},
					{op: "not_matches", args: ["@_root", "\\?ref=[0-9a-fA-F]{40}"]},
				]
			}

			diagnose: {
				severity: "warning"
				message:  "module source is not pinned to a full git commit SHA (checkov CKV_TF_1)"
			}
		}

		git_protocol_module: (_kindMatches & {
			_kind:     "module"
			_regex:    "source\\s*=\\s*\"git://"
			_message:  "module source uses the unencrypted git:// protocol"
			_severity: "error"
			_name:     "git_protocol_module"
			_doc:      "Flag module source = \"git://...\""
		}).out

		// --- provider credentials ------------------------------------------
		provider_hardcoded_credentials: (_kindMatches & {
			_kind:     "provider"
			_regex:    "(?m)^\\s*(access_key|secret_key)\\s*=\\s*\""
			_message:  "provider block hardcodes access_key or secret_key; use environment or a named profile (checkov CKV_AWS_41)"
			_severity: "error"
			_name:     "provider_hardcoded_credentials"
			_doc:      "Flag hardcoded AWS access_key/secret_key on provider blocks"
		}).out

		// --- RDS -----------------------------------------------------------
		rds_publicly_accessible: (_resourceMatches & {
			_types:    "\"aws_db_instance\"|\"aws_rds_cluster_instance\""
			_regex:    "(?m)^\\s*publicly_accessible\\s*=\\s*true"
			_message:  "RDS instance is publicly accessible (checkov CKV_AWS_17)"
			_severity: "error"
			_name:     "rds_publicly_accessible"
			_doc:      "Flag publicly_accessible = true on RDS instances"
		}).out

		rds_unencrypted: (_resourceLacks & {
			_types:    "\"aws_db_instance\"|\"aws_rds_cluster\""
			_regex:    "(?m)^\\s*storage_encrypted\\s*=\\s*true"
			_message:  "RDS storage is not encrypted (checkov CKV_AWS_16)"
			_severity: "warning"
			_name:     "rds_unencrypted"
			_doc:      "Flag RDS resources missing storage_encrypted = true"
		}).out

		rds_hardcoded_password: (_resourceMatches & {
			_types:    "\"aws_db_instance\"|\"aws_rds_cluster\""
			_regex:    "(?m)^\\s*password\\s*=\\s*\""
			_message:  "RDS password is a string literal; use a variable or secrets manager"
			_severity: "error"
			_name:     "rds_hardcoded_password"
			_doc:      "Flag password = \"...\" on RDS resources"
		}).out

		// --- EBS -----------------------------------------------------------
		ebs_unencrypted: (_resourceLacks & {
			_types:    "\"aws_ebs_volume\""
			_regex:    "(?m)^\\s*encrypted\\s*=\\s*true"
			_message:  "EBS volume is not encrypted (checkov CKV_AWS_3)"
			_severity: "warning"
			_name:     "ebs_unencrypted"
			_doc:      "Flag aws_ebs_volume missing encrypted = true"
		}).out

		ebs_device_unencrypted: (_kindMatches & {
			_kind:     "ebs_block_device"
			_regex:    "(?m)^\\s*encrypted\\s*=\\s*false"
			_message:  "instance EBS block device has encrypted = false (checkov CKV_AWS_8)"
			_severity: "warning"
			_name:     "ebs_device_unencrypted"
			_doc:      "Flag ebs_block_device { encrypted = false }"
		}).out

		root_device_unencrypted: (_kindMatches & {
			_kind:     "root_block_device"
			_regex:    "(?m)^\\s*encrypted\\s*=\\s*false"
			_message:  "instance root block device has encrypted = false (checkov CKV_AWS_8)"
			_severity: "warning"
			_name:     "root_device_unencrypted"
			_doc:      "Flag root_block_device { encrypted = false }"
		}).out

		// --- S3 -------------------------------------------------------------
		s3_public_acl: (_resourceMatches & {
			_types:    "\"aws_s3_bucket\"|\"aws_s3_bucket_acl\""
			_regex:    "(?m)^\\s*acl\\s*=\\s*\"(public-read|public-read-write|authenticated-read|website)\""
			_message:  "S3 ACL grants public or authenticated-user access (checkov CKV_AWS_20)"
			_severity: "error"
			_name:     "s3_public_acl"
			_doc:      "Flag public S3 ACL values"
		}).out

		s3_public_access_block_disabled: (_resourceMatches & {
			_types:    "\"aws_s3_bucket_public_access_block\""
			_regex:    "(?m)^\\s*(block_public_acls|block_public_policy|ignore_public_acls|restrict_public_buckets)\\s*=\\s*false"
			_message:  "S3 public access block has a protection set to false (checkov CKV_AWS_53-56)"
			_severity: "error"
			_name:     "s3_public_access_block_disabled"
			_doc:      "Flag aws_s3_bucket_public_access_block attributes set to false"
		}).out

		// --- security groups -----------------------------------------------
		sg_ingress_ssh: (_kindMatches & {
			_kind:     "ingress"
			_regex:    "(?s)0\\.0\\.0\\.0/0.*from_port\\s*=\\s*22\\b|from_port\\s*=\\s*22\\b[\\s\\S]*0\\.0\\.0\\.0/0"
			_message:  "security group allows SSH (22) from 0.0.0.0/0 (checkov CKV_AWS_24)"
			_severity: "error"
			_name:     "sg_ingress_ssh"
			_doc:      "Flag ingress blocks that open port 22 to the world"
		}).out

		sg_ingress_rdp: (_kindMatches & {
			_kind:     "ingress"
			_regex:    "(?s)0\\.0\\.0\\.0/0.*from_port\\s*=\\s*3389\\b|from_port\\s*=\\s*3389\\b[\\s\\S]*0\\.0\\.0\\.0/0"
			_message:  "security group allows RDP (3389) from 0.0.0.0/0 (checkov CKV_AWS_25)"
			_severity: "error"
			_name:     "sg_ingress_rdp"
			_doc:      "Flag ingress blocks that open port 3389 to the world"
		}).out

		sg_ingress_all: (_kindMatches & {
			_kind:     "ingress"
			_regex:    "(?s)0\\.0\\.0\\.0/0.*(protocol\\s*=\\s*\"-1\"|from_port\\s*=\\s*0\\b)|(?:protocol\\s*=\\s*\"-1\"|from_port\\s*=\\s*0\\b)[\\s\\S]*0\\.0\\.0\\.0/0"
			_message:  "security group allows all traffic from 0.0.0.0/0 (checkov CKV_AWS_277)"
			_severity: "error"
			_name:     "sg_ingress_all"
			_doc:      "Flag ingress blocks that open all ports/protocols to the world"
		}).out

		sg_rule_ssh: (_resourceMatches & {
			_types:    "\"aws_security_group_rule\"|\"aws_vpc_security_group_ingress_rule\""
			_regex:    "(?s)(0\\.0\\.0\\.0/0|cidr_ipv4\\s*=\\s*\"0\\.0\\.0\\.0/0\")[\\s\\S]*from_port\\s*=\\s*22\\b|from_port\\s*=\\s*22\\b[\\s\\S]*(0\\.0\\.0\\.0/0|cidr_ipv4\\s*=\\s*\"0\\.0\\.0\\.0/0\")"
			_message:  "security group rule allows SSH (22) from 0.0.0.0/0 (checkov CKV_AWS_24)"
			_severity: "error"
			_name:     "sg_rule_ssh"
			_doc:      "Flag standalone SG ingress rules that open port 22 to the world"
		}).out

		// --- EC2 / launch templates ----------------------------------------
		instance_imdsv1: (_resourceLacks & {
			_types:    "\"aws_instance\"|\"aws_launch_template\"|\"aws_launch_configuration\""
			_regex:    "http_tokens\\s*=\\s*\"required\""
			_message:  "instance metadata service is not forced to IMDSv2 (checkov CKV_AWS_79)"
			_severity: "warning"
			_name:     "instance_imdsv1"
			_doc:      "Flag EC2 launch resources missing metadata_options.http_tokens = \"required\""
		}).out

		instance_public_ip: (_resourceMatches & {
			_types:    "\"aws_instance\"|\"aws_launch_template\"|\"aws_launch_configuration\""
			_regex:    "(?m)^\\s*associate_public_ip_address\\s*=\\s*true"
			_message:  "instance associates a public IP (checkov CKV_AWS_88)"
			_severity: "warning"
			_name:     "instance_public_ip"
			_doc:      "Flag associate_public_ip_address = true"
		}).out

		// --- load balancers ------------------------------------------------
		alb_listener_http: (_resourceMatches & {
			_types:    "\"aws_lb_listener\"|\"aws_alb_listener\""
			_regex:    "(?m)^\\s*protocol\\s*=\\s*\"HTTP\""
			_message:  "load balancer listener uses HTTP instead of HTTPS (checkov CKV_AWS_2)"
			_severity: "warning"
			_name:     "alb_listener_http"
			_doc:      "Flag aws_lb_listener protocol = \"HTTP\""
		}).out

		// --- SNS / SQS -----------------------------------------------------
		sns_unencrypted: (_resourceLacks & {
			_types:    "\"aws_sns_topic\""
			_regex:    "(?m)^\\s*kms_master_key_id\\s*="
			_message:  "SNS topic is not encrypted with a KMS key (checkov CKV_AWS_26)"
			_severity: "warning"
			_name:     "sns_unencrypted"
			_doc:      "Flag aws_sns_topic missing kms_master_key_id"
		}).out

		sqs_unencrypted: (_resourceLacks & {
			_types:    "\"aws_sqs_queue\""
			_regex:    "(?m)^\\s*(kms_master_key_id\\s*=|sqs_managed_sse_enabled\\s*=\\s*true)"
			_message:  "SQS queue is not encrypted (checkov CKV_AWS_27)"
			_severity: "warning"
			_name:     "sqs_unencrypted"
			_doc:      "Flag aws_sqs_queue missing KMS or SQS-managed encryption"
		}).out

		// --- IAM -----------------------------------------------------------
		iam_admin_policy: (_resourceMatches & {
			_types:    "\"aws_iam_policy\"|\"aws_iam_role_policy\"|\"aws_iam_user_policy\"|\"aws_iam_group_policy\"|\"aws_iam_role\""
			_regex:    "(?s)(\"Action\"\\s*:\\s*\"\\*\"|Action\\s*=\\s*\"\\*\"|actions\\s*=\\s*\\[\\s*\"\\*\"\\s*\\])[\\s\\S]*(\"Resource\"\\s*:\\s*\"\\*\"|Resource\\s*=\\s*\"\\*\"|resources\\s*=\\s*\\[\\s*\"\\*\"\\s*\\])|(?s)(\"Resource\"\\s*:\\s*\"\\*\"|Resource\\s*=\\s*\"\\*\"|resources\\s*=\\s*\\[\\s*\"\\*\"\\s*\\])[\\s\\S]*(\"Action\"\\s*:\\s*\"\\*\"|Action\\s*=\\s*\"\\*\"|actions\\s*=\\s*\\[\\s*\"\\*\"\\s*\\])"
			_message:  "IAM policy grants Action * on Resource * (checkov CKV_AWS_1)"
			_severity: "error"
			_name:     "iam_admin_policy"
			_doc:      "Flag IAM policies that allow full admin privileges"
		}).out

		// --- EKS -----------------------------------------------------------
		eks_public_endpoint: (_resourceLacks & {
			_types:    "\"aws_eks_cluster\""
			_regex:    "(?m)^\\s*endpoint_public_access\\s*=\\s*false"
			_message:  "EKS cluster API endpoint is publicly reachable (checkov CKV_AWS_39)"
			_severity: "warning"
			_name:     "eks_public_endpoint"
			_doc:      "Flag aws_eks_cluster missing endpoint_public_access = false"
		}).out

		// --- Azure ---------------------------------------------------------
		azure_storage_http: (_resourceMatches & {
			_types:    "\"azurerm_storage_account\""
			_regex:    "(?m)^\\s*(enable_https_traffic_only|https_traffic_only_enabled)\\s*=\\s*false"
			_message:  "Azure storage account allows HTTP (checkov CKV_AZURE_3)"
			_severity: "error"
			_name:     "azure_storage_http"
			_doc:      "Flag azurerm_storage_account HTTPS-only disabled"
		}).out

		azure_nsg_ssh_open: (_resourceMatches & {
			_types:    "\"azurerm_network_security_rule\""
			_regex:    "(?s)(source_address_prefix\\s*=\\s*\"\\*\"|source_address_prefixes\\s*=\\s*\\[[^\\]]*\"[*\"]|0\\.0\\.0\\.0/0)[\\s\\S]*destination_port_range\\s*=\\s*\"22\"|destination_port_range\\s*=\\s*\"22\"[\\s\\S]*(source_address_prefix\\s*=\\s*\"\\*\"|0\\.0\\.0\\.0/0)"
			_message:  "Azure NSG allows SSH (22) from any source (checkov CKV_AZURE_10)"
			_severity: "error"
			_name:     "azure_nsg_ssh_open"
			_doc:      "Flag azurerm_network_security_rule opening SSH to the world"
		}).out

		// --- GCP -----------------------------------------------------------
		gcp_firewall_ssh_open: (_resourceMatches & {
			_types:    "\"google_compute_firewall\""
			_regex:    "(?s)0\\.0\\.0\\.0/0[\\s\\S]*\"22\"|\"22\"[\\s\\S]*0\\.0\\.0\\.0/0"
			_message:  "GCP firewall allows SSH (22) from 0.0.0.0/0 (checkov CKV_GCP_2)"
			_severity: "error"
			_name:     "gcp_firewall_ssh_open"
			_doc:      "Flag google_compute_firewall opening SSH to the world"
		}).out

		gke_legacy_abac: (_resourceMatches & {
			_types:    "\"google_container_cluster\""
			_regex:    "(?m)^\\s*enable_legacy_abac\\s*=\\s*true"
			_message:  "GKE cluster enables legacy ABAC (checkov CKV_GCP_7)"
			_severity: "error"
			_name:     "gke_legacy_abac"
			_doc:      "Flag google_container_cluster enable_legacy_abac = true"
		}).out
	}
}
