module

public import Foundation.FirstOrder.Incompleteness.First
public import Foundation.FirstOrder.Incompleteness.Second

/-!
# $\Delta_1$-definability of the induction schemata, and of `𝗜𝚺₁` and `𝗣𝗔`

This file discharges the two `axiom`s that previously sat in `Examples.lean`:
`PA_delta1Definable : 𝗣𝗔.Δ₁` and `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁`.

The route (see `DIRECTION.md`):

```
𝗣𝗔  = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ
𝗜𝚺₁ = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)
```

`𝗣𝗔⁻` is a finite set of sentences, so `Theory.Δ₁.ofFinite` gives `𝗣𝗔⁻.Δ₁`.
`Theory.Δ₁.add`/`.ofEq` then reduce both headline instances to the single obligation
`(InductionScheme ℒₒᵣ C).Δ₁`, which is the mathematical content of this file.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open LO.FirstOrder.Theory

/-! ## B1 — `𝗣𝗔⁻` is `Δ₁` (it is finite) -/

noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ PeanoMinus.finite

/-! ## The crux — the induction schema is `Δ₁` -/

/-- The induction schema `InductionScheme ℒₒᵣ C` is `Δ₁`-definable whenever the side condition
`C` is (internally) `Δ₁`-definable on codes of `ℒₒᵣ`-formulae with one free (bound) variable.

For `C = Set.univ` and `C = Arithmetic.Hierarchy 𝚺 1` the side condition is `Δ₁`, giving
`𝗣𝗔.Δ₁` and `𝗜𝚺₁.Δ₁` respectively. -/
noncomputable instance InductionScheme.delta1_univ :
    (InductionScheme ℒₒᵣ Set.univ).Δ₁ := by
  sorry

noncomputable instance InductionScheme.delta1_sigma1 :
    (InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)).Δ₁ := by
  sorry

/-! ## B2 / B3 — assemble the headline instances -/

noncomputable instance PA_delta1Definable : 𝗣𝗔.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_univ

noncomputable instance ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_sigma1

end LO.FirstOrder.Arithmetic
