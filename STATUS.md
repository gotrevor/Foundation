# STATUS — Foundation Δ₁-definability burndown 📊 ✅ COMPLETE

**Discharge `𝗣𝗔.Δ₁` / `𝗜𝚺₁.Δ₁` axioms by PROVING them.** · **Build**: 🟢 green (full `lake build Foundation`, 1672 jobs) · **`src/` sorry-free** · **Updated**: lap 2026-06-23f · DONE

## Where it stands
**BOTH headlines PROVEN & axiom-clean.** The two former `axiom`s in `Examples.lean` are now
real `instance`s in `InductionSchemeDelta1.lean`, and `Examples.lean` has **no `axiom`**:
- `PA_delta1Definable : 𝗣𝗔.Δ₁` → `#print axioms` = `[propext, Classical.choice, Quot.sound]`
- `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁` → `[propext, Classical.choice, Quot.sound]`

The burn-down **propagated downstream**: the Gödel separations `𝗣𝗔 ⪱ 𝗣𝗔 + 𝗣𝗔.Con` and
`𝗜𝚺₁ ⪱ 𝗜𝚺₁ + 𝗜𝚺₁.Con` (Examples.lean) are now axiom-clean too — Gödel I/II for the standard
theories are unconditionally machine-checked. `InductionSchemeDelta1.lean` is sorry-free; the
`--done-when` target is met.

## What's happened (newest first)
- **2026-06-23 (lap f)**: ⭐⭐ **`ISigma1_delta1Definable` PROVEN axiom-clean — project COMPLETE.**
  Built the internal `IsSigma1 : V → Prop` Δ₁ predicate (fixpoint mirroring `FormalizedFormula`,
  with a `qqBall` helper for the flat bounded-∀ clause), proved correctness `IsSigma1 ⌜ψ⌝ ↔
  Hierarchy 𝚺 1 ψ` (⟸ `sigma₁_induction'`; ⟹ meta `rec'` + `IsSigma1.of_all` + positivity helper
  `termBV_termBShift_le`), then integrated via `chSigma1 = chUniv + IsSigma1 K` →
  `chSigma1_mem_iff` → `delta1_sigma1`. Sub-lemmas: `le_termBShift`, `IsUTerm.termBShift`,
  `quote_ball`, `termBShift_quote`. Full Foundation green, both headlines + downstream axiom-clean.
- **2026-06-23 (lap e, review)**: Confirmed PA axiom-clean; mapped the full IΣ₁ build via Explore.
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
### Done — nothing blocking. Headline theorems complete & axiom-clean.
### Optional follow-ups (NOT required by this run's done-when)
- Re-pin the downstream Goodstein-independence dep onto this branch's HEAD.
- Offer the branch upstream to FFL (discharges their disclosed Δ₁-definability TODO).

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `PA_delta1Definable : 𝗣𝗔.Δ₁` | unconditional (disclosed Foundation TODO) | `[propext, Classical.choice, Quot.sound]` | 🟢 **DONE** |
| `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁` | unconditional (disclosed Foundation TODO) | `[propext, Classical.choice, Quot.sound]` | 🟢 **DONE** (lap f) |
| `InductionScheme.delta1_univ` (PA crux) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE |
| `InductionScheme.delta1_sigma1` (IΣ₁ crux) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE (lap f) |
| `isSigma1_iff_hierarchy` (correctness spine) | — | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE |
| `𝗣𝗔 ⪱ 𝗣𝗔 + 𝗣𝗔.Con` (downstream Gödel) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 axiom-clean (burn-down propagated) |

Math-axiom count on the headlines: **0** (pure trust base) — this is a *definability* result, no
deep cited theorems. No `sorryAx`, no custom axiom, anywhere in the chain.

## Pointers: DIRECTION.md (frozen plan) · newest HANDOFF-2026-06-23f · PENDING_WORK.md
