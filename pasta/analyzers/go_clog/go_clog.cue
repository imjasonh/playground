// go_clog flags printf-style clog calls.
//
// clog.Infof, clog.Errorf, and the Contextf variants format a string
// and drop the key/value attributes clog and slog are for. Log with
// clog.Info (or slog.Info) and attributes instead.
//
// A call whose function text starts with clog. is one of these,
// including clog.FromContext(ctx).Errorf and clog.With(...).Fatalf.
// Infof, Warnf, Debugf, and every Contextf method are flagged on any
// receiver. Errorf and Fatalf on a plain variable are not, because
// those names are also testing.T and the standard log package, and
// this checker has no types.

package go_clog

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

#printf: "^(Info|Warn|Error|Debug|Fatal)(Context)?f$"

#diagnose: {
	message:  "printf-style clog call; use clog.Info (or slog) with attributes"
	severity: "warning"
}

go_clog: schema.#Analyzer & {
	name:    "go_clog"
	version: "0.1.0"
	doc:     "Flag clog.Infof and the other printf-style clog calls"

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
	}
}
