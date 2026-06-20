# HANDOFF — Foundation mathlib v4.31.0 forward-port (2026-06-20, lap 2)

## 👉 READ `DIRECTION.md` + `~/src/mathlib-bump-cookbook/v4.29.1-to-v4.31.0.md` FIRST.
Objective: drive `lake build` GREEN under mathlib v4.31.0. **No theorem to prove — green build IS the headline.**

## State
- **Branch `mathlib-v4.31`**, HEAD = latest WIP commit (see `git log`).
- **Huge progress this lap.** Build went from first break at module **~1363/1671** to first break at
  **~1572/1671** — i.e. ~210 modules of Foundation now compile that didn't. **~60 source files fixed**
  across FirstOrder, Modal, InterpretabilityLogic, LinearLogic, Propositional.
- **Faithfulness intact: ZERO sorries/admits/axioms added.** Every fix is a real mechanical adaptation.
  (A raw `grep sorry` shows ~61 but that counts docstring/comment mentions; the real
  `declaration uses sorry` baseline of 27 is unchanged.)
- **Cookbook Part-3 patterns** (P–U: the `simpa`-defeq workhorse, inductive-binder, instance→def,
  meta-import, grind-no-longer-reduces-match, finite-Set-grind) are staged in
  `COOKBOOK-ADDITIONS-v4.31.md` + an entry in `ON-LINE-REQUEST.md` asking a networked host to merge
  them (the cookbook is read-only from this sandbox).

## Remaining RED files (≈6, all in the last ~100 modules) — next-lap targets

1. **`FirstOrder/Interpretation.lean`** — HIGHEST VALUE (unblocks `SetTheory/Z`,
   `Incompleteness/ProvabilityAbstraction/Basic`, `Arithmetic/Q/Basic`). The big
   `def compDirectTranslation` (~l.427) has **multiple internal field-proof failures** that each leave the
   def with metavariables → a cascade of `(kernel) declaration has metavariables` + `_def`
   type-mismatch + LCNF/noncomputable-compile errors at l.466-578. These are **symptoms, not causes** —
   fix each internal `simpa`/tactic (l.112 done, l.429 done; next is l.~433 `simp made no progress`,
   then the `func_defined`/`rel_defined` proofs) and the cascade clears. Pattern-F throughout
   (`π.Dom x` = `Eval ![x] π.domain` via `dom_iff` rfl; `∃⁰[d] φ` = `∃⁰ (d ⋏ φ)` via `exs`). Use
   `have h := …; simp only […] at h; exact h`.

2. **`LinearLogic/FirstOrder/ClassicalEmbedding.lean`** (l.129, 451). Need the **Tait→Hilbert
   provability bridge**: `⊢ᵀ Sequent.forget [↑φ]` → `𝐋𝐊 ⊢! ↑(forget φ)`. `forget_rew` (l.67) already
   gives `forget (Rew.emb φ) = Rew.emb (forget φ)`. The missing piece is how `𝐋𝐊 ⊢! ψ` (FirstOrder
   `Proof` provability) relates **definitionally** to `⊢ᵀ [emb ψ]` — trace `FirstOrder.Proof.cast` and
   the LK `instEntailment`. Once known: `⟨by simp only […]; exact Derivation.forget this.get⟩`. Same
   shape at 451 (`toLL`/Girard).

3. **`FirstOrder/SetTheory/Universe.lean`** (l.139, `ind`). l.132 (`rec_mk`) FIXED (→`exact`). l.139:
   convert `hs : Functor.Liftp P s` to `∀ y ∈ mk s.set, P y`. `liftp_iff` (l.63) does the Liftp→∀∈
   step. Blockers: (a) `Universe := QPF.Fix UniverseFunctor` def-wrapper makes `y ∈ ↑s : Set Universe`
   vs `Set (QPF.Fix UF)` non-syntactic (defeq — needs `exact`, not `simpa`); (b) `mem_mk` wants a
   `Small ↑↑s` instance that fails to synth from the `Small s.set` instance (l.36). Likely fix:
   `rw [liftp_iff] at hs; intro y hy; exact hs y (show y ∈ s from …)` with the coe handled explicitly
   (try `Universe.mem_def`/`mem_def'` l.98-100, or `@mem_mk` with explicit instance arg).

4. **`FirstOrder/SetTheory/Z.lean`** — depends on Universe; recheck after #3.

5. **`FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean`** + **`FirstOrder/Arithmetic/Q/Basic.lean`**
   — depend on Interpretation; recheck after #1.

6. **`Modal/Logic/D/Basic.lean`** (independent). l.214: pattern-F — `Set.IsWF.min_mem … : min ∈ s₂` vs
   goal `↑m ∈ s` (set/coe mismatch; needs the right `have h := …; simp at h; exact h` with the membership
   lemma). l.362: a `grind` failure (likely a Sum/finite-match — apply the
   `simp only [Frame.Rel', Frame.root, default]`-then-grind or explicit-witness recipe from the cookbook).

## Workflow that worked this lap (use it)
- `lake build 2>&1 | grep -E "error:|✖"` → fix first file in dep order → iterate one file with
  `lake env lean Foundation/Path/File.lean`.
- **Dominant break = pattern F** (`simpa`'s new syntactic final check over a defeq). Fixes, in order of
  preference: `exact h` (pure defeq) → `have h := term; simp [opts] at h; exact h` (term needs simp) →
  `simp only [opts]; exact h` (goal needs simp). See cookbook P + `COOKBOOK-ADDITIONS-v4.31.md`.
- **`grind` no longer reduces `match` on `Sum`/`Formula` constructors** → `simp only [Frame.Rel',
  Frame.root, default]` to expose, or an explicit proof (cookbook T).
- **`instance` with a non-class return type or non-inferable explicit arg** → make it `lemma`/`def`
  (cookbook R; hit in Hull, LoewenheimSkolem, Minimal, Veltman, SubLanguage).

## Completion protocol (DIRECTION "COMPLETION")
When `lake build` is fully GREEN + committed: write `~/src/.treadmill/Foundation.stop` with exactly
`source=lap` / `mode=build-green` / `reason=mathlib v4.31.0 forward-port complete — lake build green`,
commit a final HANDOFF, end. Host re-verifies green + that sorry count ≤ 27.
