// go_clog flags clog and log-setup mistakes.
//
// Printf-style calls (clog.Infof, clog.Errorf, and the Contextf
// variants) format a string and drop the key/value attributes clog
// and slog are for. Log with attributes instead. A call whose
// function text starts with clog. is one of these, including
// clog.FromContext(ctx).Errorf and clog.With(...).Fatalf. Infof,
// Warnf, Debugf, and every Contextf method are flagged on any
// receiver. Errorf and Fatalf on a plain variable are not, because
// those names are also testing.T and the standard log package, and
// this checker has no types.
//
// clog.Info, clog.Warn, clog.Error, clog.Debug, and clog.With call
// the default logger. That is slog. Keep clog.Fatal: slog has no
// equivalent, and Fatal logs then exits. Keep clog for a logger
// stored on a context: clog.FromContext, clog.WithLogger, and the
// Context methods.
//
// gcp.NewHandler builds the Cloud Logging handler itself. Blank-import
// github.com/chainguard-dev/clog/gcp/init instead. Which programs run
// on GCP is not visible from the syntax, so a missing blank import is
// not flagged.
//
// flag.String and StringVar whose name contains log-level parse a
// level as a string. Use github.com/chainguard-dev/clog/slag. A
// slog.Level passed to flag.TextVar is left alone, because kube stays
// on slog and has no slag dependency.

package go_clog

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

#printf: "^(Info|Warn|Error|Debug|Fatal)(Context)?f$"

#diagnose: {
	message:  "printf-style clog call; use slog (or a context logger) with attributes"
	severity: "warning"
}

go_clog: schema.#Analyzer & {
	name:    "go_clog"
	version: "0.3.0"
	doc:     "Flag printf-style clog calls, default-logger clog calls, gcp.NewHandler, and string log-level flags"

	facts: {}

	rules: {
		clog_printf: {
			name: "clog_printf"
			doc:  "clog.Infof, clog.FromContext(ctx).Errorf, and the other printf-style calls on clog"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "call_expression"
				fields: function: {
					capture: "fnexpr"
					pattern: {
						node: "selector_expression"
						fields: field: {capture: "fn", pattern: gopat.FieldIdentifier}
					}
				}
				where: [
					{op: "matches", args: ["@fn", #printf]},
					{op: "matches", args: ["@fnexpr", "^clog\\."]},
				]
			}

			diagnose: #diagnose
		}

		method_printf: {
			name: "method_printf"
			doc:  "Infof, Warnf, Debugf, and Contextf methods, which are clog's printf API"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "call_expression"
				fields: function: {
					capture: "fnexpr"
					pattern: {
						node: "selector_expression"
						fields: field: {capture: "fn", pattern: gopat.FieldIdentifier}
					}
				}
				where: [
					{op: "matches", args: ["@fn", "^(Info|Warn|Debug)f$|^(Info|Warn|Error|Debug|Fatal)Contextf$"]},
					{op: "not_matches", args: ["@fnexpr", "^clog\\."]},
				]
			}

			diagnose: #diagnose
		}

		default_logger: {
			name: "default_logger"
			doc:  "clog.Info and the other package-level calls, which use the default logger"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "call_expression"
				fields: function: {
					capture: "fnexpr"
					pattern: {
						node: "selector_expression"
						fields: field: {capture: "fn", pattern: gopat.FieldIdentifier}
					}
				}
				where: [
					{op: "matches", args: ["@fn", "^(Info|Warn|Error|Debug|With)$"]},
					{op: "matches", args: ["@fnexpr", "^clog\\.(Info|Warn|Error|Debug|With)$"]},
				]
			}

			diagnose: {
				message:  "clog call on the default logger; use slog, or pass a logger on the context"
				severity: "warning"
			}
		}

		gcp_new_handler: {
			name: "gcp_new_handler"
			doc:  "gcp.NewHandler; blank-import clog/gcp/init instead"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				where: [
					{op: "eq", args: ["@pkg", "gcp"]},
					{op: "eq", args: ["@fn", "NewHandler"]},
				]
			}

			diagnose: {
				message:  "gcp.NewHandler; blank-import github.com/chainguard-dev/clog/gcp/init"
				severity: "warning"
			}
		}

		string_log_level: {
			name: "string_log_level"
			doc:  "flag.String or FlagSet.String whose name contains log-level"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [{
						capture: "name"
						pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
					}]
				}
				where: [
					{op: "eq", args: ["@fn", "String"]},
					{op: "matches", args: ["@name", "(?i)\"[^\\\"]*log[-_]?level"]},
				]
			}

			diagnose: {
				message:  "string flag for a log level; use github.com/chainguard-dev/clog/slag"
				severity: "warning"
			}
		}

		string_var_log_level: {
			name: "string_var_log_level"
			doc:  "flag.StringVar or FlagSet.StringVar whose name contains log-level"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [
						gopat.Any,
						{
							capture: "name"
							pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
						},
					]
				}
				where: [
					{op: "eq", args: ["@fn", "StringVar"]},
					{op: "matches", args: ["@name", "(?i)\"[^\\\"]*log[-_]?level"]},
				]
			}

			diagnose: {
				message:  "string flag for a log level; use github.com/chainguard-dev/clog/slag"
				severity: "warning"
			}
		}
	}
}
