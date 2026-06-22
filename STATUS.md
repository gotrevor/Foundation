# STATUS — Foundation Δ₁-definability burndown 📊

**Discharge `𝗣𝗔.Δ₁` / `𝗜𝚺₁.Δ₁` axioms by PROVING them.** · **Build**: 🟢 green (deliverable module compiles; 2 disclosed crux sorries) · **Updated**: lap 2026-06-22 (late) · `39fdc94`

## Where it stands
The two former `axiom`s (`PA_delta1Definable : 𝗣𝗔.Δ₁`, `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁`) are now
*declarations assembled from real instances* in `InductionSchemeDelta1.lean` via
`Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_{univ,sigma1}`. `PeanoMinus.delta1` (B1) is
**proven & axiom-clean**. Everything reduces to the single crux `(InductionScheme ℒₒᵣ C).Δ₁`, attacked
by a DECODE recognizer. The **mathematical keystone** — the `bv`-pin bridge that pins the universal-closure
arity to `fvSup` (forbidding over-recognition by vacuous leading `∀`s) — is **proven & axiom-clean** as of
this lap. What remains for `delta1_univ` is mechanical Δ₁-formula *assembly* + `mem_iff` packaging; then
the Σ₁ side-condition for `delta1_sigma1`.

## What's happened (newest first)
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
### Short-term (mirror PENDING_WORK top)
1. Extract `indBody.val : V → V` (or inline) as a `𝚺₁`-graph for the recognizer clause.
2. Assemble the concrete `ch : 𝚫₁.Semisentence 1` from combinators; prove `DefinedPred R ch` (⇒ `ProperOn`
   free via `Defined.proper`). `Theory.Δ₁.ch` needs a CONCRETE semisentence (Definable is a Prop).
3. `mem_iff` over ℕ — forward (compose proven bridges) + backward (inversion bijection + `IsSemiformula.sound`),
   reusing `bv_quote_fixitr` to pin `m = fvSup`.
4. Package `delta1_univ` ⇒ **`PA_delta1Definable` axiom-clean** (clears B2/PA).
### Long-term
5. `delta1_sigma1`: `delta1_univ` core + internal "K is Σ₁" predicate (the side condition `Cᵢ` for
   `C = Hierarchy 𝚺 1`). Search arithmetized `Hierarchy`/`𝚺`-class machinery before building.
### To completion
- `Examples.lean`: delete both `axiom`s, `import InductionSchemeDelta1`. `#print axioms` on both instances
  = `[propext, Classical.choice, Quot.sound]`. Then re-pin downstream Goodstein dep; offer branch to FFL.

## Axiom ledger (the fidelity spine)
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `PA_delta1Definable : 𝗣𝗔.Δ₁` | unconditional (disclosed Foundation TODO) | `sorryAx` (+ trust base) | 🔴 *in progress* — sorryAx is the crux `delta1_univ`; NOT a real open conjecture, it's the obligation being discharged. Target: trust base only. |
| `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁` | unconditional (disclosed Foundation TODO) | `sorryAx` (+ trust base) | 🔴 *in progress* — sorryAx is `delta1_sigma1`. Target: trust base only. |
| `PeanoMinus.delta1 : 𝗣𝗔⁻.Δ₁` (B1) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE |
| `bv_quote_fixitr` (crux keystone) | — | `[propext, Classical.choice, Quot.sound]` | 🟢 DONE |

Math-axiom count on the headlines once complete: **0** (pure trust base) — this is a *definability*
result, no deep cited theorems. The current `sorryAx` is the work-in-progress crux, not a 🔴 conjecture.

## Pointers: DIRECTION.md (frozen plan) · newest HANDOFF-2026-06-22-2359 (+ this lap's) · PENDING_WORK.md
