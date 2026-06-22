# STATUS — Foundation Δ₁-definability burndown 📊

**Discharge `𝗣𝗔.Δ₁` / `𝗜𝚺₁.Δ₁` axioms by PROVING them.** · **Build**: 🟢 green (deliverable compiles; **1** disclosed crux sorry = `delta1_sigma1`) · **Updated**: lap 2026-06-23e · `68cc6eb`

## Where it stands
The two former `axiom`s are now *declarations assembled from real instances* in
`InductionSchemeDelta1.lean`. **`PA_delta1Definable : 𝗣𝗔.Δ₁` is PROVEN & axiom-clean**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`) — headline #1 of 2 DONE. The
**only** remaining `sorry` is `InductionScheme.delta1_sigma1` (the `C = Hierarchy 𝚺 1` case),
which feeds `ISigma1_delta1Definable` (headline #2). Plan locked (this lap): build an internal
`IsSigma1 : V → Prop` Δ₁ predicate (fixpoint, mirroring `FormalizedFormula`) with correctness
`IsSigma1 ⌜ψ⌝ ↔ Hierarchy 𝚺 1 ψ`, then `chSigma1 = chUniv + IsSigma1 K`. The done-when target
(`InductionSchemeDelta1.lean` sorry-free) halts the run the moment `delta1_sigma1` lands.

## What's happened (newest first)
- **2026-06-23 (lap e, review)**: Confirmed PA axiom-clean; only `delta1_sigma1` open. Mapped the
  full IΣ₁ build via Explore — all bridge lemmas located (`quote_{rel,nrel,and,or,all,ex}` in
  Formula/Coding.lean, `qqNLT`/`lt_qqNLT_right`/`ltIndex`, `typed_quote_bShift`, `Rew.positive_iff`
  = `t.Positive ↔ ∃t', t = bShift t'`, `Semiformula.{cases',rec'}`, `le_of_nth_le_nth`+`adjoin_le_adjoin`
  for the one missing sub-lemma `le_termBShift`). ⟸ via `sigma₁_induction'`; ⟹ via meta `rec'` on ψ
  + per-constructor `IsSigma1` inversions (decode bounded-∀ `^∀(qqNLT(^#0)u ^⋎ q)`). Executing now.
- **2026-06-22 (late)**: ⭐ Cracked the keystone `bv_quote_fixitr : bv ⌜fixitr 0 (fvSup χ) ▹ χ⌝ = fvSup χ`
  (over ℕ), axiom-clean. Route: level-factoring via `IsSemiformula.sound` + `subst_comp_fixitr` (no meta
  `bvSup` needed). Added supporting `Semiterm/Semiformula.quote_castLE` + `.freeVariables_castLE`
  (`Rew.castLE` preserves raw code & free vars). Navigated the V=ℕ model cast/order instance soup via
  `natCast_nat` (model cast on ℕ = id) + model `<` = `Nat.lt`.
- **2026-06-22 (2359)**: forward-direction recognizer machinery complete & axiom-clean — `quote_univCl_eq`,
  `subst_fvarVec_quote` (raw closure inversion), `fvarVec` (Σ₁ vec `⟨^&0..^&(k-1)⟩`), `indBody`/`indBody_quote`,
  `typed_quote_succInd`, `fvar?_fvSup_pred` ("sup attained").
- **2026-06-22 (earlier)**: `qqAlls` (internal iterated-∀, Σ₁) + `quote_allClosure`; refined DECODE recognizer
  design (no internal `fvSup`/`fixitr` needed). B1 (`Set.Finite 𝗣𝗔⁻` → `𝗣𝗔⁻.Δ₁`) done.

## Outstanding
### Short-term (mirror PENDING_WORK top) — all in service of `delta1_sigma1`
1. `le_termBShift : IsUTerm L t → t ≤ termBShift L t` (sub-lemma; `IsUTerm.induction` + `le_of_nth_le_nth`/`adjoin_le_adjoin`).
2. `IsSigma1` fixpoint: `Phi`/`phi_iff`/`blueprint`(σ,π)/`construction`(`defined`,`monotone`)/`StrongFinite`/`IsSigma1`/`isSigma1`/Δ₁ instance + `case_iff`/`mk` + per-constructor inversions. Port `wip/IsSigma1-draft.lean`, fix the 5 blockers.
3. Correctness `IsSigma1 (⌜ψ⌝:ℕ) ↔ Hierarchy 𝚺 1 ψ`: ⟸ `sigma₁_induction'`; ⟹ meta `rec'` + decode.
4. Integrate: `InductionSigma1R`, `chSigma1` (= chUniv + IsSigma1 K), `chSigma1_mem_iff`, `delta1_sigma1`.
### To completion
- Both instances axiom-clean ⇒ done-when fires. (`Examples.lean` already imports the module; axioms already deleted.)
  Then re-pin downstream Goodstein dep; offer branch to FFL.

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `PA_delta1Definable : 𝗣𝗔.Δ₁` | unconditional (disclosed Foundation TODO) | `[propext, Classical.choice, Quot.sound]` | 🟢 **DONE** — verified axiom-clean lap 2026-06-23d. |
| `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁` | unconditional (disclosed Foundation TODO) | `sorryAx` (+ trust base) | 🔴 *in progress* — sorryAx is `delta1_sigma1`; NOT an open conjecture, it's the obligation being discharged. Target: trust base only. |
| `PeanoMinus.delta1 : 𝗣𝗔⁻.Δ₁` (B1) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE |
| `InductionScheme.delta1_univ` (PA crux) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE |

Math-axiom count on the headlines once complete: **0** (pure trust base) — this is a *definability*
result, no deep cited theorems. The remaining `sorryAx` is the work-in-progress crux, not a 🔴 conjecture.

## Pointers: DIRECTION.md (frozen plan) · newest HANDOFF-2026-06-22-2359 (+ this lap's) · PENDING_WORK.md
