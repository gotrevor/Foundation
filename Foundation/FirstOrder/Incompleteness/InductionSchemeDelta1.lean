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

namespace LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## Internal iterated universal quantifier `qqAlls`

`qqAlls p k = ^∀ ^∀ … ^∀ p` (`k` quantifiers), the internal counterpart of the meta universal
closure `∀⁰*`. This is part (a) of arithmetizing `univCl` (part (b), the free→bound `fixitr`
rewrite, is still open). The headline of this section is `quote_allClosure`:
`⌜∀⁰* φ⌝ = qqAlls ⌜φ⌝ n`. -/

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

section qqAlls

def qqAlls.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqAllDef y ih”

noncomputable def qqAlls.construction : PR.Construction V qqAlls.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∀ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqAll]

/-- `qqAlls p k = ^∀ ^∀ ... ^∀ p` (`k` universal quantifiers). -/
noncomputable def qqAlls (p k : V) : V := qqAlls.construction.result ![p] k

@[simp] lemma qqAlls_zero (p : V) : qqAlls p 0 = p := by simp [qqAlls, qqAlls.construction]

@[simp] lemma qqAlls_succ (p k : V) : qqAlls p (k + 1) = ^∀ (qqAlls p k) := by
  simp [qqAlls, qqAlls.construction]

section

def _root_.LO.FirstOrder.Arithmetic.qqAllsDef : 𝚺₁.Semisentence 3 :=
  qqAlls.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqAlls_defined : 𝚺₁-Function₂ (qqAlls : V → V → V) via qqAllsDef := .mk
  fun v ↦ by simp [qqAlls.construction.result_defined_iff, qqAllsDef]; rfl

instance qqAlls_definable : 𝚺₁-Function₂ (qqAlls : V → V → V) := qqAlls_defined.to_definable

instance qqAlls_definable' (Γ) : Γ-[m + 1]-Function₂ (qqAlls : V → V → V) := qqAlls_definable.of_sigmaOne

end

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma le_qqAll (p : V) : p ≤ ^∀ p := by
  simp only [qqAll]; exact le_trans (le_pair_right _ _) le_self_add

/-- `^∀` commutes through the closure -/
lemma qqAlls_all (p k : V) : qqAlls (^∀ p) k = ^∀ (qqAlls p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, ih, qqAlls_succ]

/-- pushing one more `^∀` onto the body equals one more layer of closure -/
lemma qqAlls_succ' (p k : V) : qqAlls p (k + 1) = qqAlls (^∀ p) k := by
  rw [qqAlls_succ, qqAlls_all]

@[simp] lemma le_qqAlls (p k : V) : p ≤ qqAlls p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    refine le_trans ih ?_
    rw [qqAlls_succ]
    exact le_qqAll _

lemma succ_le_qqAll (p : V) : p + 1 ≤ ^∀ p := by
  simp only [qqAll]; exact add_le_add (le_pair_right _ _) (le_refl 1)

/-- the number of quantifiers is bounded by the closure code (bounds `∃ m ≤ p`) -/
@[simp] lemma index_le_qqAlls (p k : V) : k ≤ qqAlls p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ]
    exact le_trans (add_le_add ih (le_refl 1)) (succ_le_qqAll _)

@[simp] lemma isUFormula_qqAlls {p k : V} : IsUFormula L (qqAlls p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ, IsUFormula.all, ih]

lemma bv_qqAlls {p k : V} (hp : IsUFormula L p) : bv L (qqAlls p k) = bv L p - k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ, bv_all (isUFormula_qqAlls.mpr hp), ih, Arithmetic.sub_sub]

/-- closing `k` variables of an `(n+k)`-formula yields an `n`-formula -/
lemma IsSemiformula.qqAlls {n k p : V} (h : IsSemiformula L (n + k) p) :
    IsSemiformula L n (qqAlls p k) := by
  rw [isSemiformula_iff] at h ⊢
  obtain ⟨hu, hbv⟩ := h
  refine ⟨isUFormula_qqAlls.mpr hu, ?_⟩
  rw [bv_qqAlls hu, tsub_le_iff_right]
  exact hbv

/-- The internal iterated-`^∀` computes the universal-closure code:
`⌜∀⁰* φ⌝ = qqAlls ⌜φ⌝ n`. -/
lemma quote_allClosure {n : ℕ} (φ : SyntacticSemiformula L n) :
    (⌜(∀⁰* φ : SyntacticFormula L)⌝ : V) = qqAlls (⌜φ⌝ : V) (n : V) := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [show (∀⁰* φ : SyntacticFormula L) = ∀⁰* (∀⁰ φ) from rfl]
    have := ih (∀⁰ φ)
    rw [Semiformula.quote_all] at this
    rw [this, Nat.cast_succ, qqAlls_succ']

/-- The Gödel code of a sentence `univCl ψ` agrees with that of its `SyntacticFormula`
unfolding `univCl' ψ` (which prepends `fvSup ψ` universals to the `fixitr`-rewritten body). -/
lemma quote_univCl (ψ : SyntacticFormula L) :
    (⌜Semiformula.univCl ψ⌝ : V) = (⌜Semiformula.univCl' ψ⌝ : V) := by
  show (⌜(Rewriting.emb (Semiformula.univCl ψ) : SyntacticFormula L)⌝ : V) = ⌜Semiformula.univCl' ψ⌝
  congr 1
  simp [Semiformula.univCl]

/-- `⌜univCl' ψ⌝ = qqAlls ⌜fixitr 0 (fvSup ψ) ▹ ψ⌝ (fvSup ψ)`: the universal closure is the
internal iterated-`^∀` applied to the freevar-free `fixitr`-image of `ψ`. -/
lemma quote_univCl' (ψ : SyntacticFormula L) :
    (⌜Semiformula.univCl' ψ⌝ : V)
      = qqAlls (⌜(Rew.fixitr 0 ψ.fvSup ▹ ψ : SyntacticSemiformula L (0 + ψ.fvSup))⌝ : V)
          ((0 + ψ.fvSup : ℕ) : V) := by
  rw [Semiformula.univCl']; exact quote_allClosure _

/-- Combined: the code of the universal closure of `ψ`. -/
lemma quote_univCl_eq (ψ : SyntacticFormula L) :
    (⌜Semiformula.univCl ψ⌝ : V)
      = qqAlls (⌜(Rew.fixitr 0 ψ.fvSup ▹ ψ : SyntacticSemiformula L (0 + ψ.fvSup))⌝ : V)
          ((0 + ψ.fvSup : ℕ) : V) := by
  rw [quote_univCl, quote_univCl']

/-- **Closure inversion at the code level.** Substituting the free-variable atoms `&0 … &(m-1)`
back into the `fixitr`-image recovers `⌜φ⌝`. This is the DECODE direction: the recognizer can
recover `⌜succInd ψ⌝` (hence `ψ`) from the freevar-free closure body using the *already-proven*
internal `subst`, with no need for an internal `fixitr`. Meta witness: `subst_comp_fixitr`. -/
lemma quote_subst_fvar_fixitr (φ : SyntacticFormula L) :
    (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : SyntacticSemiformula L (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L))⌝ : V) = ⌜φ⌝ := by
  rw [show (Rew.fixitr 0 φ.fvSup ▹ φ : SyntacticSemiformula L (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L)) = φ from by
    have := Semiformula.subst_comp_fixitr (L := L) φ
    convert this using 2]

end qqAlls

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

open LO.FirstOrder.Theory

/-! ## B1 — `𝗣𝗔⁻` is `Δ₁` (it is finite) -/

noncomputable instance PeanoMinus.delta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ PeanoMinus.finite

/-! ## Typed decomposition of `succInd`

The crux relates the code `⌜univCl (succInd φ)⌝` to internal primitives. The macro `!φ t` in
formula position desugars to `φ ⇜ ![t]` (`Rew.substs`, **not** `embSubsts` as an earlier handoff
claimed), so `⌜succInd φ⌝` collapses under the *already-present* `typed_quote_substs`/`map_imply`/
`LCWQIsoGödelQuote.all` simp set — no `typed_quote_embSubsts` bridge is needed. -/

section succInd

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- `succInd φ`, simplified (the `∀ x, !φ x` instances are the identity substitution `φ ⇜ ![#0]`). -/
lemma succInd_eq (φ : Semiformula ℒₒᵣ ℕ 1) :
    succInd φ =
      ((φ ⇜ (![‘0’] : Fin 1 → Semiterm ℒₒᵣ ℕ 0))
        🡒 ((∀⁰ (φ 🡒 (φ ⇜ (![‘#0 + 1’] : Fin 1 → Semiterm ℒₒᵣ ℕ 1)))) 🡒 ∀⁰ φ)) := by
  unfold succInd; simp

/-- The typed Gödel code of the induction axiom body, built from the typed code `⌜φ⌝` purely with
the existing typed constructors (`subst`, `🡒`, `∀⁰`). -/
lemma typed_quote_succInd (φ : Semiformula ℒₒᵣ ℕ 1) :
    (⌜succInd φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0) =
      (⌜φ ⇜ (![‘0’] : Fin 1 → Semiterm ℒₒᵣ ℕ 0)⌝)
        🡒 ((∀⁰ (⌜φ⌝ 🡒 ⌜φ ⇜ (![‘#0 + 1’] : Fin 1 → Semiterm ℒₒᵣ ℕ 1)⌝)) 🡒 ∀⁰ ⌜φ⌝) := by
  unfold succInd
  rw [show φ ⇜ (![#0] : Fin 1 → Semiterm ℒₒᵣ ℕ 1) = φ from by simp]
  simp

/-- The typed `succInd` shape as a function of the (typed) core code `K = ⌜ψ⌝`. The recognizer
checks `subst (fvarVec m) b = (indBody K).val` to recover the core `K` and verify the body has
the induction-axiom shape. -/
noncomputable def indBody (K : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 0 :=
  (K.subst ![⌜(‘0’ : Semiterm ℒₒᵣ ℕ 0)⌝])
    🡒 ((∀⁰ (K 🡒 K.subst ![⌜(‘#0 + 1’ : Semiterm ℒₒᵣ ℕ 1)⌝])) 🡒 ∀⁰ K)

/-- `indBody ⌜ψ⌝ = ⌜succInd ψ⌝`: the typed reconstruction matches the actual code. -/
lemma indBody_quote (φ : Semiformula ℒₒᵣ ℕ 1) :
    indBody (⌜φ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) = ⌜succInd φ⌝ := by
  rw [typed_quote_succInd]; unfold indBody; simp [Matrix.constant_eq_singleton]

end succInd

/-! ## The crux — the induction schema is `Δ₁` -/

/-- The induction schema `InductionScheme ℒₒᵣ C` is `Δ₁`-definable whenever the side condition
`C` is (internally) `Δ₁`-definable on codes of `ℒₒᵣ`-formulae with one free (bound) variable.

The recognizer is `ch(p) := ∃ q ≤ p, IsSemiformula 1 q ∧ Cᵢ q ∧ inductionAxiom q = p`, where
`inductionAxiom : V → V` is the `Σ₁` function with `inductionAxiom ⌜ψ⌝ = ⌜univCl (succInd ψ)⌝`.
Its construction (and the one genuinely hard piece — the internal universal closure of `succInd`)
is laid out in `PENDING_WORK.md`; build at the typed `Bootstrapping.Semiformula` layer.

For `C = Set.univ` (side condition `⊤`) this gives `𝗣𝗔.Δ₁`; for `C = Arithmetic.Hierarchy 𝚺 1`
(side condition "ψ is internally `Σ₁`") it gives `𝗜𝚺₁.Δ₁`. -/
noncomputable instance InductionScheme.delta1_univ :
    (InductionScheme ℒₒᵣ Set.univ).Δ₁ := by
  sorry -- TODO(crux, C=univ): see PENDING_WORK.md Path A. Win = #print axioms clean.

noncomputable instance InductionScheme.delta1_sigma1 :
    (InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)).Δ₁ := by
  sorry -- TODO(crux, C=Σ₁): delta1_univ core + internal Σ₁-formula predicate (P3b).

/-! ## B2 / B3 — assemble the headline instances -/

noncomputable instance PA_delta1Definable : 𝗣𝗔.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_univ

noncomputable instance ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 InductionScheme.delta1_sigma1

end LO.FirstOrder.Arithmetic
