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

/-- **Sup attained.** The largest free-variable index of `φ` is `fvSup φ - 1` (when `φ` has free
variables). Together with `lt_fvSup_of_fvar?` this pins `fvSup` as exactly the count of universals
in `univCl'`, and is what the recognizer's `bv b = m` clause checks (no over-recognition by padding
leading `∀`s). -/
lemma _root_.LO.FirstOrder.Semiformula.fvar?_fvSup_pred {L : Language} {n : ℕ}
    (φ : SyntacticSemiformula L n) (h : 0 < φ.fvSup) : φ.FVar? (φ.fvSup - 1) := by
  by_cases he : φ.freeVariables = ∅
  · simp [Semiformula.fvSup, he] at h
  · obtain ⟨k, hk⟩ := Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
    rw [show φ.fvSup = k + 1 from by simp [Semiformula.fvSup, hk]]
    simpa using Finset.mem_of_max hk

/-! ## `castLE`-invariance of the Gödel code and free variables

Raising the de Bruijn level of a (semi)term/(semi)formula by `Rew.castLE` changes neither its raw
Gödel code (the underlying variable indices are preserved) nor its set of free variables. These are
the bookkeeping lemmas behind the `bv`-pin bridge below: an `IsSemiformula j`-witness of a code that
"really" sits at level `n ≥ j` factors through `castLE`, letting us read off the free-variable
budget. -/

section castLE

variable {L : Language} [L.Encodable] [L.LORDefinable]

private lemma semitermVec_val_congr {k m m' : ℕ}
    (g : Fin k → Bootstrapping.Semiterm V L m) (g' : Fin k → Bootstrapping.Semiterm V L m')
    (h : ∀ i, (g i).val = (g' i).val) :
    Bootstrapping.SemitermVec.val g = Bootstrapping.SemitermVec.val g' := by
  unfold Bootstrapping.SemitermVec.val
  congr 1
  funext i
  exact h i

lemma _root_.LO.FirstOrder.Semiterm.quote_castLE {n : ℕ} (t : SyntacticSemiterm L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (⌜(Rew.castLE h t : SyntacticSemiterm L n')⌝ : V) = ⌜t⌝ := by
  induction t with
  | bvar x => intro n' h; simp
  | fvar x => intro n' h; simp
  | func f v ih =>
      intro n' h
      simp only [Rew.func, Semiterm.quote_func]
      rw [semitermVec_val_congr (fun i ↦ ⌜Rew.castLE h (v i)⌝) (fun i ↦ ⌜v i⌝)
        (fun i ↦ by rw [← Semiterm.quote_def, ← Semiterm.quote_def]; exact ih i h)]

lemma _root_.LO.FirstOrder.Semiterm.freeVariables_castLE {n : ℕ} (t : SyntacticSemiterm L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (Rew.castLE h t : SyntacticSemiterm L n').freeVariables = t.freeVariables := by
  induction t with
  | bvar x => intro n' h; simp
  | fvar x => intro n' h; simp
  | func f v ih =>
      intro n' h
      simp only [Rew.func, Semiterm.freeVariables_func]
      apply Finset.biUnion_congr rfl
      intro i _; exact ih i h

lemma _root_.LO.FirstOrder.Semiformula.quote_castLE {n : ℕ} (φ : SyntacticSemiformula L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (⌜(Rew.castLE h ▹ φ : SyntacticSemiformula L n')⌝ : V) = ⌜φ⌝ := by
  induction φ using Semiformula.rec' with
  | hverum => intro n' h; simp
  | hfalsum => intro n' h; simp
  | hrel r v =>
      intro n' h
      simp only [Semiformula.rew_rel, Semiformula.quote_rel]
      rw [semitermVec_val_congr (fun i ↦ ⌜Rew.castLE h (v i)⌝) (fun i ↦ ⌜v i⌝)
        (fun i ↦ by rw [← Semiterm.quote_def, ← Semiterm.quote_def]; exact Semiterm.quote_castLE _ h)]
  | hnrel r v =>
      intro n' h
      simp only [Semiformula.rew_nrel, Semiformula.quote_nrel]
      rw [semitermVec_val_congr (fun i ↦ ⌜Rew.castLE h (v i)⌝) (fun i ↦ ⌜v i⌝)
        (fun i ↦ by rw [← Semiterm.quote_def, ← Semiterm.quote_def]; exact Semiterm.quote_castLE _ h)]
  | hand φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_and, Semiformula.quote_and, ihp h, ihq h]
  | hor φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_or, Semiformula.quote_or, ihp h, ihq h]
  | hall φ ih => intro n' h; rw [Rewriting.app_all, Semiformula.quote_all, Rew.q_castLE, ih, Semiformula.quote_all]
  | hexs φ ih => intro n' h; rw [Rewriting.app_exs, Semiformula.quote_ex, Rew.q_castLE, ih, Semiformula.quote_ex]

lemma _root_.LO.FirstOrder.Semiformula.freeVariables_castLE {n : ℕ} (φ : SyntacticSemiformula L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (Rew.castLE h ▹ φ : SyntacticSemiformula L n').freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' with
  | hverum => intro n' h; simp
  | hfalsum => intro n' h; simp
  | hrel r v =>
      intro n' h
      simp only [Semiformula.rew_rel, Semiformula.freeVariables_rel]
      apply Finset.biUnion_congr rfl; intro i _; exact Semiterm.freeVariables_castLE _ h
  | hnrel r v =>
      intro n' h
      simp only [Semiformula.rew_nrel, Semiformula.freeVariables_nrel]
      apply Finset.biUnion_congr rfl; intro i _; exact Semiterm.freeVariables_castLE _ h
  | hand φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_and, Semiformula.freeVariables_and, ihp h, ihq h]
  | hor φ ψ ihp ihq => intro n' h; simp only [LogicalConnective.HomClass.map_or, Semiformula.freeVariables_or, ihp h, ihq h]
  | hall φ ih => intro n' h; simp only [Rewriting.app_all, Semiformula.freeVariables_all, Rew.q_castLE, ih]
  | hexs φ ih => intro n' h; simp only [Rewriting.app_exs, Semiformula.freeVariables_exs, Rew.q_castLE, ih]

end castLE

/-! ## The `bv`-pin bridge

The recognizer pins the number of leading universals `m` to `fvSup` of the core formula via a clause
forcing `bv b = m`. Soundness of that pin rests on the bridge below: the freevar-free universal-closure
body uses *exactly* `fvSup χ` bound slots, so closing fewer than `fvSup χ` quantifiers cannot reach a
sentence — forbidding over-recognition by vacuous leading `∀`s. -/

section bvPin

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- **`bv`-pin bridge** (over ℕ): `bv ⌜fixitr 0 (fvSup χ) ▹ χ⌝ = fvSup χ`.
- `≤` is immediate from `quote_univCl_eq` + `bv_qqAlls` (closing `fvSup` quantifiers reaches a
  sentence, whose `bv` is `0`).
- `≥` is by level-factoring: were the body an `IsSemiformula j` for some `j < fvSup`, `IsSemiformula.sound`
  + `castLE`-invariance would re-express `χ` as `γ ⇜ ![&0, …, &(j-1)]` with `γ` free-variable-free,
  forcing `fvSup χ ≤ j < fvSup χ`. -/
lemma bv_quote_fixitr (χ : SyntacticFormula L) :
    bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup := by
  -- the freevar-free closure body
  have not_fvar_body : ∀ x, ¬(Rew.fixitr 0 χ.fvSup ▹ χ).FVar? x := by
    intro x
    rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
    simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
    intro hh
    rcases Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
    · simp at hz
    · have : z < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
      simp [this] at hx
  have hbsemi := Semiformula.quote_isSemiformula (V := ℕ)
    (Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))
  have hbU : IsUFormula L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))⌝ : ℕ) :=
    hbsemi.isUFormula
  -- `≤` direction: the body has `0 + fvSup` bound slots, so `bv ≤ fvSup` (model order over ℕ).
  -- On ℕ the model cast is the identity (`natCast_nat`) and `<` is `Nat.lt`.
  have hle := hbsemi.bv_le
  simp only [Nat.zero_add, natCast_nat] at hle
  -- the model `≤` on ℕ unfolds to `= ∨ <` with `<` the standard `Nat.lt`
  rcases (hle : bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup ∨ bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))⌝ : ℕ)
      < χ.fvSup) with heq | hlt
  · exact heq
  -- `hlt : bv ⌜body⌝ < χ.fvSup` ; this case is impossible (forbids vacuous leading `∀`s)
  exfalso
  set j := bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))⌝ : ℕ) with hj
  have hpos : 0 < χ.fvSup := by omega
  have hsemi : IsSemiformula L j (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))⌝ : ℕ) := by
    have := IsUFormula.isSemiformula hbU; rwa [← hj] at this
  obtain ⟨γ, hγ⟩ := IsSemiformula.sound hsemi
  have hjle : j ≤ 0 + χ.fvSup := by omega
  -- codes agree across levels, hence the formulas agree
  have hcast : (Rew.castLE hjle ▹ γ : SyntacticSemiformula L (0 + χ.fvSup))
      = (Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup)) := by
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp
    rw [Semiformula.quote_castLE, hγ]
  -- `γ` is free-variable-free
  have hγfree : γ.freeVariables = ∅ := by
    have hb : (Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup)).freeVariables = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx ↦ not_fvar_body x hx
    have := Semiformula.freeVariables_castLE γ hjle
    rw [hcast, hb] at this; exact this.symm
  -- invert the closure: `χ = γ ⇜ ![&0, …, &(j-1)]`
  have hχeq : χ = γ ⇜ (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) := by
    have e1 : (Rew.fixitr 0 χ.fvSup ▹ χ : SyntacticSemiformula L (0 + χ.fvSup))
        ⇜ (fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L)) = χ := Semiformula.subst_comp_fixitr χ
    have hRewEq : (Rew.subst (fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L))).comp (Rew.castLE hjle)
        = Rew.subst (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) := by
      ext x <;> simp [Rew.comp_app, Fin.coe_castLE]
    symm
    rw [← e1, ← hcast]
    unfold Rewriting.subst
    rw [← TransitiveRewriting.comp_app, hRewEq]
  -- contradiction: `&(fvSup-1)` occurs in `χ`, but the inversion bounds free vars by `j ≤ fvSup-1`
  have hfv : (γ ⇜ (fun i : Fin j ↦ (&↑i : SyntacticTerm L))).FVar? (χ.fvSup - 1) := by
    rw [← hχeq]; exact Semiformula.fvar?_fvSup_pred χ hpos
  unfold Rewriting.subst at hfv
  rcases Semiformula.fvar?_rew hfv with (⟨i, hi⟩ | ⟨z, hz, _⟩)
  · have hib : χ.fvSup - 1 = (i : ℕ) := by
      simpa [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
    have hij := i.isLt
    omega
  · simp [Semiformula.FVar?, hγfree] at hz

end bvPin

/-! ## Internal free-variable vector `fvarVec`

`fvarVec k = ⟨^&0, ^&1, …, ^&(k-1)⟩`, the code of the substitution vector mapping bound var `#i`
to free var `&i`. The recognizer applies `subst (fvarVec m) ·` to invert the universal closure
(undo `fixitr`), recovering `⌜succInd ψ⌝` from the freevar-free body — see `quote_subst_fvar_fixitr`.
This is a `𝚺₁` vector recursion (`fvarVec (k+1) = concat (fvarVec k) (^&k)`). -/

section fvarVec

def fvarVec.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih n. ∃ f, !qqFvarDef f n ∧ !concatDef y ih f”

noncomputable def fvarVec.construction : PR.Construction V fvarVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun _ n ih ↦ concat ih (^&n)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

/-- `fvarVec k = ⟨^&0, …, ^&(k-1)⟩`. -/
noncomputable def fvarVec (k : V) : V := fvarVec.construction.result ![] k

@[simp] lemma fvarVec_zero : fvarVec (0 : V) = 0 := by simp [fvarVec, fvarVec.construction]

@[simp] lemma fvarVec_succ (k : V) : fvarVec (k + 1) = concat (fvarVec k) (^&k) := by
  simp [fvarVec, fvarVec.construction]

def _root_.LO.FirstOrder.Arithmetic.fvarVecDef : 𝚺₁.Semisentence 2 := fvarVec.blueprint.resultDef

instance fvarVec_defined : 𝚺₁-Function₁ (fvarVec : V → V) via fvarVecDef := .mk
  fun v ↦ by simp [fvarVec.construction.result_defined_iff, fvarVecDef]; rfl

instance fvarVec_definable : 𝚺₁-Function₁ (fvarVec : V → V) := fvarVec_defined.to_definable

instance fvarVec_definable' (Γ) : Γ-[m + 1]-Function₁ (fvarVec : V → V) := fvarVec_definable.of_sigmaOne

@[simp] lemma len_fvarVec (k : V) : len (fvarVec k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

/-- `fvarVec k` is the vector with `i`-th entry `^&i` for `i < k`. -/
lemma nth_fvarVec (k : V) : ∀ i < k, (fvarVec k).[i] = ^&i := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | rfl
    · rw [fvarVec_succ, concat_nth_lt _ _ (by simpa using hlt)]; exact ih i hlt
    · rw [fvarVec_succ, concat_nth_len' _ _ (by simp)]

/-- `fvarVec` is the code of the typed substitution vector `fun i ↦ ^&i` (over a standard length). -/
lemma fvarVec_val_eq (m : ℕ) :
    fvarVec ((m : ℕ) : V)
      = SemitermVec.val (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) := by
  apply nth_ext (by simp)
  intro i hi
  rw [len_fvarVec] at hi
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
  have hj : j < m := by exact_mod_cast hi
  rw [nth_fvarVec _ _ hi, show ((j : ℕ) : V) = ((⟨j, hj⟩ : Fin m) : ℕ) from rfl]
  rw [SemitermVec.val_nth_eq (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) ⟨j, hj⟩]
  simp

/-- **Raw closure inversion.** `subst (fvarVec (fvSup φ)) ⌜fixitr 0 (fvSup φ) ▹ φ⌝ = ⌜φ⌝`: the
internal substitution by `fvarVec` undoes the universal-closure `fixitr` at the code level. This
is the recognizer's mechanism for recovering `⌜succInd ψ⌝` from the freevar-free closure body. -/
lemma subst_fvarVec_quote (φ : SyntacticFormula ℒₒᵣ) :
    Bootstrapping.subst ℒₒᵣ (fvarVec ((0 + φ.fvSup : ℕ) : V))
        (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : SyntacticSemiformula ℒₒᵣ (0 + φ.fvSup))⌝ : V)
      = (⌜φ⌝ : V) := by
  set Kt : Bootstrapping.Semiformula V ℒₒᵣ (0 + φ.fvSup) :=
    ⌜(Rew.fixitr 0 φ.fvSup ▹ φ : SyntacticSemiformula ℒₒᵣ (0 + φ.fvSup))⌝ with hKt
  set w : SemitermVec V ℒₒᵣ (0 + φ.fvSup) 0 :=
    (fun i : Fin (0 + φ.fvSup) ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) with hw
  rw [fvarVec_val_eq,
    show (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : SyntacticSemiformula ℒₒᵣ (0 + φ.fvSup))⌝ : V) = Kt.val from rfl,
    show Bootstrapping.subst ℒₒᵣ w.val Kt.val = (Kt.subst w).val from rfl,
    ← quote_subst_fvar_fixitr (V := V) φ]
  congr 1
  rw [hKt]
  simp only [FirstOrder.Semiformula.typed_quote_substs, hw, Semiterm.typed_quote_fvar]

/-- **Generalized free-ization.** For *any* `β : SyntacticSemiformula ℒₒᵣ m`, substituting the
free-variable atoms `&0 … &(m-1)` for its `m` bound slots equals `⌜β ⇜ (&·)⌝`. This is the forward
recognizer's tool: once `IsSemiformula.sound` yields a `β` with `⌜β⌝ = b`, this computes
`subst (fvarVec m) b`. (Specializes to `subst_fvarVec_quote` when `β` is a `fixitr`-image.) -/
lemma subst_fvarVec_quote' {m : ℕ} (β : SyntacticSemiformula ℒₒᵣ m) :
    Bootstrapping.subst ℒₒᵣ (fvarVec ((m : ℕ) : V)) (⌜β⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : V) := by
  set Kt : Bootstrapping.Semiformula V ℒₒᵣ m := ⌜β⌝ with hKt
  set w : SemitermVec V ℒₒᵣ m 0 :=
    (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V ℒₒᵣ 0)) with hw
  rw [fvarVec_val_eq,
    show (⌜β⌝ : V) = Kt.val from rfl,
    show Bootstrapping.subst ℒₒᵣ w.val Kt.val = (Kt.subst w).val from rfl]
  rw [show (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0).val from rfl]
  congr 1
  rw [hKt]
  simp only [FirstOrder.Semiformula.typed_quote_substs, hw, Semiterm.typed_quote_fvar]

end fvarVec

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
