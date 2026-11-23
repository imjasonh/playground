// lean_deprecated renames Lean core lemmas that Lean deprecated in
// favor of a lemma with the same arguments, so the rename can't change
// what a proof elaborates to. Lean v4.34.0 deprecates these (since
// 2026-07-21):
//
//   if_pos   -> ite_eq_left   (hc : c)    : ite c t e = t
//   if_neg   -> ite_eq_right  (hnc : ¬c)  : ite c t e = e
//   if_true  -> ite_true      (t e : α)   : ite True t e = t
//   if_false -> ite_false     (t e : α)   : ite False t e = e
//
// Only the bare name matches. A qualified name such as `Nat.if_pos`
// or `_root_.if_pos` is a different identifier and is left alone.
// Lean's own build prints these as `has been deprecated` warnings,
// one per use. Add a name to `renames` only when the replacement's
// explicit and implicit arguments match the deprecated lemma's.
package lean_deprecated

import (
	"github.com/imjasonh/pasta/schema"
	leanlang "github.com/imjasonh/pasta/lang/lean"
)

_renames: {
	if_pos:   "ite_eq_left"
	if_neg:   "ite_eq_right"
	if_true:  "ite_true"
	if_false: "ite_false"
}

lean_deprecated: schema.#Analyzer & {
	name:    "lean_deprecated"
	version: "0.1.0"
	doc:     "Rename deprecated Lean core lemmas to their drop-in replacements"
	facts: {}

	rules: {
		for old, new in _renames {
			(old): {
				name:      old
				doc:       "`\(old)` is deprecated; use `\(new)`"
				languages: [leanlang.Name]
				requires: []
				provides: []

				match: {
					node: "identifier"
					where: [{op: "eq", args: ["@_root", old]}]
				}

				diagnose: {
					severity: "warning"
					message:  "`\(old)` is deprecated; use `\(new)`"
				}

				rewrite: edits: [{target: "_root", replacement: new}]
			}
		}
	}
}
