#!/usr/bin/env python3
"""Writes the loops of `sigstore::verify` whose step depends on what one
pass parses, each from a segment or stage that returns to the loop's head
and the stage that leaves it.

The step is a relation (`svChain` strings `k` of them together): the body's
success condition, with its witnesses, and the loop variables' new values.
The theorem is by induction on a bound on the fuel, a length that every pass
lowers. The loops:

- `SvCosigLoop.lean`: the checkpoint's signature lines, `sv_seg_cosig` until
  `w5c` is 0, then `sv_csx`. The state includes the signature found so far.
- `SvEkuLoop.lean`: the OIDs of an `ExtKeyUsage` value, `sv_deku2` until
  `cl` is 0, then `sv_deku3`.

Usage: python3 scripts/gen-sv-relloop.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import IDENT, Chain, Stage, lean_binders, param_key, strip_parens, subst, top_split  # noqa: E402
from svloop import GLOBAL, Loop, invariants  # noqa: E402
from svmerge import sc_pattern  # noqa: E402
from svseg import canon, strip_exists  # noqa: E402



def find(proofs, rx):
    """The name of the body's fact that matches `rx`."""
    return next(nm for nm, piece in proofs if re.fullmatch(rx, canon(strip_exists(piece))))


def cosig_slice(proofs, names1):
    nl = find(proofs, r"nlScan M0 w38 0 w5c\.toNat = some \w+")
    return {'sg_in': f"(by rw [svSubOfNat_toNat (by have := (nlScan_lt _ _ _ {nl}).2; omega)]; "
                     f"exact (sg_in).nlRest {nl})"}


def cosig_dec(proofs, names1):
    nl = find(proofs, r"nlScan M0 w38 0 w5c\.toNat = some \w+")
    ix = names1[names1.index(nl) - 1]
    return f"svRem_le1 (a := {ix} + 1) (N := N) (by omega) (by have := (nlScan_lt _ _ _ {nl}).2; omega) hN"


EKU_OID = r"derOid \(memBytes M0 \(?cp\)? \(?cl\)?\.toNat\) = \.ok \w+"


EXT_SEQ = r"derElement 0x30 \(memBytes M0 \(?cur\)? \(?rem\)?\.toNat\) = \.ok \w+"


def ext_slice(proofs, names1):
    return {'xl_in': f"((xl_in).restW {find(proofs, EXT_SEQ)})"}


def ext_dec(proofs, names1):
    return f"svRem_elem {find(proofs, EXT_SEQ)} hN"


def eku_slice(proofs, names1):
    return {'c_in': f"((c_in).restW (derOid_ok_elem {find(proofs, EKU_OID)}))"}


def eku_dec(proofs, names1):
    return f"svRem_elem (derOid_ok_elem {find(proofs, EKU_OID)}) hN"


SIG_OF = """/-- The signature that memory holds where the signature loop keeps a found one. -/
def svSigOf (M : Word → BitVec 8) (B : Word) : Bytes :=
  (M (B + 0x21A0 + BitVec.ofNat 32 0x10)).toNat :: memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x1480) 63

theorem svSigOf_at (M : Word → BitVec 8) (B : Word) :
    M (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 ((svSigOf M B).getD 0 0) ∧
    ∀ j, j < 63 → M (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 ((svSigOf M B).getD (1 + j) 0) := by
  refine ⟨BitVec.eq_of_toNat_eq ?_, fun j hj => BitVec.eq_of_toNat_eq ?_⟩
  · show _ = (BitVec.ofNat 8 (M (B + 0x21A0 + BitVec.ofNat 32 0x10)).toNat).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (M _).isLt]
  · rw [svSigOf, Nat.add_comm 1 j, List.getD_cons_succ, List.getD_eq_getElem?_getD, memBytes,
      List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some, add_ofNat_assoc,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (M _).isLt]"""


LOOPS = {
    'SvCosigLoop': dict(body=('SvSegCosig', 'sv_seg_cosig'), exit=('SvCsx', 'sv_csx'), name='sv_cosigloop',
                        step='sv_cosigStep', ok='sv_cosigloopOk', fuel='w5c', cond='hrem', xcond='hrem0',
                        slice=cosig_slice, dec=cosig_dec, title="the checkpoint's signature loop",
                      pick=dict(binder='sg', value="svSigOf n0.mem B",
                                hyps={'b0_10': "(svSigOf_at n0.mem B).1", 'q0_1480': "(svSigOf_at n0.mem B).2"},
                                doc="the signature that memory holds where the loop keeps a found one: before any "
                                "line, the loop has found none, so any value does.",
                                lemma=SIG_OF),
                        step_doc="One more signature line, from state `s` to `s'`: there are bytes left, and the "
                        "next line is well formed.",
                        thm_doc="The checkpoint's signature loop: `k` more lines, then the end."),
    'SvEkuLoop': dict(body=('SvDeku2', 'sv_deku2'), exit=('SvDeku3', 'sv_deku3'), name='sv_ekuloop',
                      step='sv_ekuStep', ok='sv_ekuloopOk', fuel='cl', cond='hcl', xcond='hcl',
                      slice=eku_slice, dec=eku_dec, title="an `ExtKeyUsage` value's OIDs",
                      step_doc="One more `ExtKeyUsage` OID, from state `s` to `s'`: there are bytes left, and "
                      "the next entry is an OID.",
                      thm_doc="The `ExtKeyUsage` loop: `k` more OIDs, then the end."),
    'SvExtLoop': dict(body=('SvSegExt', 'sv_seg_ext'), exit=('SvL7', 'sv_l7'), name='sv_extloop',
                      step='sv_extStep', ok='sv_extloopOk', fuel='rem', cond='hrem', xcond='hrem',
                      fixed_in={'ea_in': ('el_in', 'SvIn B p0 L.toNat', '((el_in).shrink (by omega))')},
                      slice=ext_slice, dec=ext_dec, title="the leaf's extensions",
                      step_doc="One more extension of the leaf, from state `s` to `s'`: there are bytes left, "
                      "and the next extension is one `sigstore::verify` accepts.",
                      thm_doc="The extensions loop: `k` more extensions, then the end."),
}


def success_text(sfile, sname):
    src = open(f'C3BootProofs/Proofs/{sfile}.lean').read()
    i = src.index(f'theorem {sname} ')
    st = src[i:src.index(':= by\n', i)]
    rest = st[st.index('\n    (¬'):].split('\n', 2)[2].strip()
    return rest[:-1] if rest.count(')') > rest.count('(') else rest


def main(fname, c):
    BODY, EXIT, NAME, STEP, OK, FUEL = c['body'], c['exit'], c['name'], c['step'], c['ok'], c['fuel']
    L = Loop(*BODY)
    X = Stage(*EXIT)
    st, head, loopv = L.st, L.head, L.loopv
    # An exit binder that names what the body states about the same register
    # or frame word is the body's value.
    xb = {b for names, _ in lean_binders(*EXIT) for b in names}
    bp = dict(st.params)
    xmap, xconv = {}, {}
    for p, t in X.params:
        if param_key(p) and p in bp:
            xr, br = strip_parens(top_split(t, ' = ')[-1]), strip_parens(top_split(bp[p], ' = ')[-1])
            m = re.fullmatch(r"BitVec\.ofNat 32 (\w+)", xr)
            if xr in xb and xr != br and xr not in loopv:
                xmap[xr] = br
            elif m and m.group(1) in xb and re.fullmatch(r"\w+", br):
                xmap[m.group(1)] = f"{br}.toNat"
                xconv[p] = f"({p}.trans (ofNat_toNat_self _).symm)"
    fixed_in = c.get('fixed_in', {})
    groups_, seen = [], set(loopv) | {'n0'} | set(xmap)
    for names, ty in lean_binders(*BODY) + lean_binders(*EXIT):
        new = [b for b in names if b not in seen]
        seen |= set(new)
        if new:
            groups_.append((new, ty))
    fixed = " ".join("{" + " ".join(n) + " : " + t + "}" for n, t in groups_)
    explicit = " ".join("(" + " ".join(n) + " : " + t + ")" for n, t in groups_)
    fixed_names = " ".join(b for n, _ in groups_ for b in n)
    tup = "(" + ", ".join(loopv) + ")"
    ps = [b + "'" for b in loopv]
    ptup = "(" + ", ".join(ps) + ")"
    T = " × ".join(L.types[b] for b in loopv)
    proj = {b: "s" + ".2" * j + (".1" if j + 1 < len(loopv) else "") for j, b in enumerate(loopv)}
    sc = " ∧ ".join(st.sc_parts)
    new = "(" + ", ".join(L.upd[b] for b in loopv) + ")"
    rel = subst(f"{proj[FUEL]} ≠ 0 ∧ " + (sc + " ∧ " if sc else "") + f"s' = {new}", proj)
    ok = subst(success_text(*EXIT), xmap)
    ok_k = re.sub(IDENT.format("n0"), "nk", subst(ok, dict(zip(loopv, ps))))
    typed_ps = " ".join(f"({p} : {L.types[b]})" for b, p in zip(loopv, ps))

    # The body's names, as the proof takes it apart.
    args = L.args({c['cond']: 'h0', **{p: v[2] for p, v in fixed_in.items()}})
    ch = Chain(lambda x: None)
    _, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    proofs = ch.proofs
    ov = {'F': 'F', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, _ in L.per:
        ov[p] = p
    ov.update({p: v[2] for p, v in fixed_in.items()})
    ov.update(c['slice'](proofs, names1))
    invs = invariants(L, proofs)
    for p, _, nm in invs:
        ov[p] = nm
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hn = [p for p, _ in head]
    per = [(p, t) for p, t in L.kept_per if p != c['cond'] and p not in fixed_in]
    per += [(v[0], v[1]) for v in fixed_in.values()]
    per_names = [p for p, _ in per]
    ih_args = [a for (p, _), a in zip(st.params, a2) if p in hn or p in per_names]
    ih_args += [v[0] for v in fixed_in.values()]
    xextra = [(p, subst(t, xmap)) for p, t in X.params if p not in bp and p != c['xcond']]
    ih_args += [p for p, _ in xextra]

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvSegCk")
    O(f"import C3BootProofs.Proofs.{BODY[0]}")
    O(f"import C3BootProofs.Proofs.{EXIT[0]}")
    O("")
    O(f"/-!\n# `sigstore::verify`: {c['title']}\n\nWritten by `scripts/gen-sv-relloop.py` from "
      f"`{BODY[1]}` and `{EXIT[1]}`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    O(L.opens())
    O("")
    O("set_option linter.unusedVariables false in")
    O(f"/-- {c['step_doc']} -/")
    O(f"def {STEP} {explicit} (M0 : Word → BitVec 8) : {T} → {T} → Prop :=")
    O(f"  fun s s' => {rel}")
    O("")
    O("set_option linter.unusedVariables false in")
    O(f"/-- How `{EXIT[1]}` ends once `{FUEL}` is 0. -/")
    O(f"def {OK} {explicit} (M0 : Word → BitVec 8) {typed_ps} (nk : Machine) : Prop :=")
    O(f"  {FUEL}' = 0 ∧ " + "".join(f"({subst(t, dict(zip(loopv, ps)))}) ∧ " for _, t, _ in invs) + f"({ok_k})")
    O("")
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- {c['thm_doc']} -/")
    O(f"theorem {NAME} {fixed}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL) + " :")
    O(f"    ∀ (N : Nat) " + " ".join(f"{{{b} : {L.types[b]}}}" for b in loopv) + " {n0 : Machine},")
    O(f"    (hN : {FUEL}.toNat ≤ N) →")
    for p, t in head:
        O(f"    ({p} : {t}) →")
    for p, t in per:
        O(f"    ({p} : {t}) →")
    for p, t in xextra:
        O(f"    ({p} : {t}) →")
    O(f"    SvErrRet B out v n0 ∨ ∃ k {' '.join(ps)}, svChain ({STEP} {fixed_names} M0) k {tup} {ptup} ∧")
    O("      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem nk.mem {L.kl} ∧ {OK} {fixed_names} M0 {' '.join(ps)} nk := by")
    xnamed = " ".join(f"({b} := {xmap.get(b, b)})" for b in dict.fromkeys(b for names, _ in lean_binders(*EXIT) for b in names))
    xargs = " ".join({c['xcond']: 'h0', **xconv}.get(p, p) for p, _ in X.params)
    intro = f"intro {' '.join(loopv)} n0 hN {' '.join(hn)} {' '.join(per_names)} {' '.join(p for p, _ in xextra)}"
    exit_ok = (f"exact .inr ⟨0, {', '.join(loopv)}, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), "
               f"h0, {''.join(p + ', ' for p, _, _ in invs)}okx⟩")
    O("  intro N")
    O("  induction N with")
    O("  | zero =>")
    O(f"    {intro}")
    O(f"    have h0 : {FUEL} = 0 := svRem_zero hN")
    O(f"    rcases {EXIT[1]} {xnamed} {xargs} with {X.errpat} | okx")
    O("    · exact .inl e")
    O(f"    · {exit_ok}")
    O("  | succ N ih =>")
    O(f"    {intro}")
    O(f"    by_cases h0 : {FUEL} = 0")
    O(f"    · rcases {EXIT[1]} {xnamed} {xargs} with {X.errpat} | okx")
    O("      · exact .inl e")
    O(f"      · {exit_ok}")
    O(f"    rcases {BODY[1]} {L.named()} {' '.join(args)} with {st.errpat} | ⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    O(f"    have hdec := {c['dec'](proofs, names1)}")
    O(f"    rcases ih hdec {' '.join(ih_args)} with e | ⟨k, {', '.join(ps)}, chn, nk, cs, h3, h4, hk, okk⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · exact .inr ⟨k + 1, {', '.join(ps)}, svChain.cons ⟨h0, {', '.join(names1)}, rfl⟩ chn, nk, c1.trans cs, "
      "h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩")
    O("")
    # The loop as a stage.
    pr = dict(zip(loopv, ps))
    facts = []
    for f in X.facts:
        if f.key == 'STEPS':
            continue
        t = subst(subst(f.text, xmap), pr)
        if f.key in ('r3', 'r4'):
            t = f"reg n' ({f.key[1]} : Fin 32) = reg n0 ({f.key[1]} : Fin 32)"
        elif f.key == 'KL':
            u = list(dict.fromkeys(re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", L.kl + f.text)))
            t = "SvKeepL B n0.mem n'.mem [" + ", ".join(u) + "]"
        facts.append((f.key, f"({t})" if t.startswith('∀') else t))
    xnm = sc_pattern(X)
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- `{NAME}` as a stage. -/")
    O(f"theorem {NAME}_st {fixed} {{N : Nat}} " + " ".join(f"{{{b} : {L.types[b]}}}" for b in loopv) +
      " {n0 : Machine}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL))
    O(f"    (hN : {FUEL}.toNat ≤ N)")
    for p, t in head:
        O(f"    ({p} : {t})")
    for p, t in per:
        O(f"    ({p} : {t})")
    for p, t in xextra:
        O(f"    ({p} : {t})")
    O("    :")
    O("    SvErrRet B out v n0 ∨")
    O(f"    (∃ k {' '.join(ps)}, svChain ({STEP} {fixed_names} M0) k {tup} {ptup} ∧")
    O(f"      {FUEL}' = 0 ∧" + "".join(f" ({subst(t, pr)}) ∧" for _, t, _ in invs) +
      ("" if not X.sc_parts else "\n      " + " ∧ ".join(subst(subst(x, xmap), pr) for x in X.sc_parts) + " ∧"))
    O("    ∃ n', Steps n0 n' ∧")
    O("        " + " ∧\n        ".join(t for _, t in facts) + ") := by")
    named = " ".join(f"({b} := {b})" for n, _ in groups_ for b in n)
    O(f"  rcases {NAME} {named} F hret hO M0 N hN {' '.join(hn)} {' '.join(per_names)} {' '.join(p for p, _ in xextra)} with e | "
      f"⟨k, {', '.join(ps)}, chn, nk, cs, hr3, hr4, hkl, okh⟩")
    O("  · exact .inl e")
    iv = [f"iv{j}" for j in range(len(invs))]
    O(f"  obtain ⟨hz, {', '.join(iv + xnm + ['n1', 'cn'] + [f'f_{k}' for k, _ in facts])}⟩ := okh")
    terms = [{"r3": "f_r3.trans hr3", "r4": "f_r4.trans hr4", "KL": "(hkl.trans f_KL).mono (by decide)"}.get(k, f"f_{k}")
             for k, _ in facts]
    O(f"  exact .inr ⟨k, {', '.join(ps)}, chn, hz, {', '.join(iv + xnm + ['n1', 'cs.trans cn'] + terms)}⟩")
    O("")
    pick = c.get('pick')
    if pick:
        # The loop as a stage, with a start value of one loop variable that
        # memory gives, so that no hypothesis about it is needed.
        b = pick['binder']
        O(pick['lemma'])
        O("")
        i0 = next(n for n, l in enumerate(out) if l.startswith(f"theorem {NAME}_st "))
        i1 = next(n for n, l in enumerate(out) if n > i0 and l.endswith(":= by"))
        stmt = out[i0:i1 + 1]
        stmt[0] = stmt[0].replace(f"theorem {NAME}_st ", f"theorem {NAME}_st0 ").replace(f" {{{b} : {L.types[b]}}}", "")
        stmt = [l for l in stmt if not any(l.strip().startswith(f"({h} :") for h in pick['hyps'])]
        j = next(n for n, l in enumerate(stmt) if l.startswith("    (∃ k "))
        stmt[j] = "    (∃ " + b + ", ∃ k " + stmt[j][len("    (∃ k "):]
        O("set_option maxHeartbeats 16000000 in")
        O("set_option maxRecDepth 100000 in")
        O(f"/-- `{NAME}_st` from {pick['doc']} -/")
        out.extend(stmt)
        rest = [p for p, _ in head if p not in pick['hyps']] + per_names + [p for p, _ in xextra]
        hyps = " ".join(f"({h} := {v})" for h, v in pick['hyps'].items())
        O(f"  rcases {NAME}_st ({b} := {pick['value']}) {hyps} {named} F hret hO M0 hN {' '.join(rest)} with e | h")
        O("  · exact .inl e")
        O("  · exact .inr ⟨_, h⟩")
        O("")
    O("end C3.RV32.Sv")
    O("")
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    for f in sys.argv[1:] or LOOPS:
        main(f, LOOPS[f])
