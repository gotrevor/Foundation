# Cookbook additions (to merge into ~/src/mathlib-bump-cookbook/v4.29.1-to-v4.31.0.md)

The cookbook is read-only from the Foundation YOLO sandbox, so these Part-3 patterns (discovered porting
THIS repo) are staged here for a networked host to append. Append verbatim before the final
"*Empirically grounded…*" line.

---

# Part 3 — patterns from the Foundation (modal/FO logic) port

This repo is almost all bespoke inductive proof systems + Kripke semantics, so the breaks cluster
differently than the analysis/number-theory projects above. The dominant break by FAR is `simpa`'s new
syntactic final check (pattern F) hitting **definitional unfoldings unique to this code**: `∈ S` vs the
set-as-predicate `S x`; an instance-path difference (`s.struc` vs `s.instStructureDom`); a `def`-wrapped
prop (`eqv L a b` ⇉ `op(=).val ![a,b]`, `ValidOnModel M φ` ⇉ `∀ x, Satisfies M x φ`, `M ⊧ₘ σ` ⇉ the
`Eval` form). All are *defeq* but no longer *syntactic*.

## P. `simpa using h` across a `∈`/predicate or instance-path defeq — the Foundation workhorse fix
The single most common break. `simpa [opts] using term` where, after simp, `term`'s type is defeq but not
syntactic to the goal (membership-vs-predicate, a defeq instance path, a `def`-wrapped head). Three fixes,
in increasing power:

```lean
-- 1. No simp actually needed on the goal → just exact (checks up to defeq):
--    simpa using h            ↦  exact h
-- 2. Goal needs the simp, term matches up to defeq → simp the goal, exact the term:
--    simpa [opts] using h     ↦  simp only [opts] ; exact h
-- 3. The term needs the simp (unfold a def, reindex a Finset, resolve a subst) → simp the HYP, exact:
--    simpa [opts] using term  ↦  have h := term ; simp [opts] at h ; exact h
```
Fix #3 is the default for the `Hilbert.*.axm`-style instance bodies (`HasAxiomK.K`, etc.) and for
`Derivation.sound`-style existential-unpacking. The `simp at h ⊢` variant (simp BOTH) is occasionally
needed when both the goal's `def` (e.g. `Axioms.FourN`) and the hyp must reach the same normal form.

*Gotcha A — `Ax` no longer infers.* Rewriting `simpa using C.axm (φ:=…) (s:=…) (by exact mem_X)` to
`have h := C.axm …` can strand the axiom-set metavar (`stuck at HasX ?m`) because the old goal pinned it.
If the term has no `(φ := …Ax…)` to pin it, ascribe the membership proof: `(show _ ∈ Ax from mem_X)`
instead of `(by exact mem_X)` / bare `mem_X`.

*Gotcha B — substitution composition.* `axm (s := s' ∘ s) ih` gives `… (φ⟦s'∘s⟧)` but the goal wants
`φ⟦s'⟧⟦s⟧`. `simp at h` usually rewrites it; if not, `rw [Formula.subst.def_comp] at h` (modal) is the
explicit bridge. (`Set.union_self` is the analogous explicit rewrite when a binary-relation constructor
like `GlobalConsequence.mdp` produces `X ∪ X` against a goal of `X`.)

*Batch tip.* These come in files of 10-25 near-identical `instance` bodies. A scripted
`simpa [O] using Q.axm <args>;` → `have h := Q.axm <args>; simp [O] at h; exact h;` rewrite works, BUT
watch two traps: (a) a `simpa` with the term **fully on one line and no trailing `;`** (last tactic of the
block) vs (b) a `simpa` with `(φ := …)` **on the simpa line but the term continuing** onto indented
follow-on lines — a naive "rest non-empty ⇒ single-line" heuristic mis-splits (b). Verify each file
compiles after scripting.

## Q. Inductive constructor binder `{φ}` collides with a section `variable {φ …}`
`inductive Foo (Ax) : … | mem {φ} : … → Foo Ax …` now ERRORS
`Only parameters appearing in the declaration header may have their binders kinds be overridden` when a
section `variable {φ ψ : …}` is in scope — the bare `{φ}` is read as a binder-kind *override* of that
variable, not a fresh binder. Give it a type to make it fresh (exactly as the error's Hint says):

```lean
| mem {φ : Formula α} : …          -- not  | mem {φ} : …
| subst {φ : Formula α} {s : Substitution α} : …
```

## R. `instance` with an explicit (auto-param) argument is rejected — make it a `def`
`instance foo (h : l.contains .X := by decide) : (build l).HasX where …` now ERRORS
`This instance has 1 argument that cannot be inferred using typeclass synthesis` (the autoParam `h` is
explicit, appears only as a side-condition). If it's actually consumed as a *term* (e.g. a macro emits
`instance : … := foo`, or it's applied with the autoParam defaulted), just change `instance` → `def`;
the autoParam `:= by decide` still fires at each concrete use site. (TC auto-synthesis for a *generic*
`l` never worked anyway — `decide` can't prove `l.contains .X` for a variable.)

## S. `#eval`/meta command can't see a `Repr` (or other meta) instance → `public meta import`
`#eval (… : Formula ℕ)` ERRORS `Invalid 'meta' definition '_eval', 'instRepr' is not accessible here;
consider adding 'public meta import …'`. The module system now segregates meta-time access. Add the
suggested line to the import block:

```lean
public meta import Foundation.Modal.Formula.Basic   -- alongside the existing `public import`s
```

## T. `grind` no longer reduces a `match`/iota-redex on a concrete constructor
`grind` used to whnf-reduce `match concrete with …` (and close rfl-trivial goals through it); v4.31's does
not. Two faces:
- A relation/predicate defined by `match` on `Sum`/`Formula` constructors (`x ≺[φ] y`, `(extendRoot).Rel`)
  left as an opaque `match …` in grind's e-graph. Expose the value first: `simp only [Frame.Rel', Frame.root,
  default]` (unfold to the constructor so iota fires), then `grind`/`trivial`/`rfl`/the explicit term.
  Beware: the connective `🡒`/`⋏` are **typeclass projections** (`Arrow.arrow`/`Wedge.wedge`), NOT the raw
  `Formula.imp`/`Formula.and` of the match patterns, so `simp` won't iota-reduce a `match (a 🡒 b) with
  | .imp … =>` until you unfold `[Arrow.arrow, Wedge.wedge, Top.top, Bot.bot]` (and `Formula.top_def` for `⊤`).
  When even that won't converge, drop to an explicit witness proof (e.g. `Forces.not_def_iff.mpr (Or.inl ⟨w,
  …⟩)`, discharging each `≺[concrete] y` by `show (w:Fin n) ≤ z from by decide` since `≺[]` isn't `Decidable`).
- grind can't prove a now-trivial `Sum.inl 0 = Sum.inl 0` (negates it, can't refute). Replace with `rfl`/
  `exact h rfl`/a `left; simp [..., extend]`-style direct close.

## U. finite-`Set (Fin k)` facts `grind`/`lia` used to close
A `{0,1} ≠ ({0} : Set (Fin 2))` or a contradiction from `{1} ∪ {0} ⊆ {1}` no longer falls to `grind`. Use
`simp [Set.ext_iff]` (for the inequality/extensional goal) or `simp_all [Set.subset_def]` (to explode the
subset hypothesis to a membership contradiction). `decide` does NOT work — `Set (Fin k)` isn't `Decidable`.
