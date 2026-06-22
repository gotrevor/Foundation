/-
WIP DRAFT — internal `IsSigma1` Σ₁-formula predicate for the `C = Hierarchy 𝚺 1` case
(NOT in the build target; promote into InductionSchemeDelta1.lean once green).

STATUS: structure drafted (Phi, phi_iff, blueprint σ/π, construction defined/monotone,
StrongFinite, IsSigma1 + Δ₁ instance). Compilation blockers identified, NOT yet fixed:

1. SOUNDNESS fix: the bounded-∀ clause guard `∃ t, u = termBShift t` is unbounded and unsound
   for junk `t`. Change to `∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t` and add to blueprint
   σ/π (with isUTerm.sigma/.pi). Needed so `t ≤ u` holds (next item).
2. SUB-LEMMA `le_termBShift : IsUTerm ℒₒᵣ t → t ≤ termBShift ℒₒᵣ t` — termBShift only grows
   (^#z→^#(z+1) grows, ^&x fixed, ^func recurses). Prove by `IsUTerm`/term structural induction.
   Used to bound `∃ t < p` in phi_iff (t ≤ termBShift t = u < p).
3. SUB-LEMMA `lt_qqNLT_right : y < qqNLT x y` (and maybe `lt_qqNLT_left`). qqNLT x y =
   ^nrel 2 ltIndex ?[x,y]; y = ?[x,y].[1], use `nth_lt_qqNRel_of_lt (by simp)`. Used for u < p.
4. `defined` proof: the `simp [blueprint, ... .df.iff ...]` for the σ↔π (proper) and σ↔Phi
   directions needs tuning — add isUTerm.sigma/.pi, termBShift/qqNLT graph `.df.iff`, and the
   qqBvar/qqOr/qqAll/qqNLT defs to the simp set. Mirror FormalizedFormula.construction.defined.
5. Notation: `^≮`/`^#` may not be in scope; use explicit `qqNLT`/`qqBvar`/`qqOr`/`qqAll`.

After green: CORRECTNESS `IsSigma1 ⌜ψ⌝ ↔ Hierarchy 𝚺 1 ψ` (over V):
 - (⟸) `Hierarchy.sigma₁_induction'` (Arithmetic/Basic/Hierarchy.lean:458): each case → matching
   Phi clause; bounded-∀: u = ⌜bShift t⌝ = termBShift ⌜t⌝ (needs `termBShift_quote`/`typed_quote_bShift`).
 - (⟹) `IsSemiformula.sigma1_structural_induction` (Formula/Basic.lean:1352) on the code, invert
   each Phi clause to a real subformula + apply the Hierarchy constructor; bounded-∀ inversion uses
   `Rew.positive_iff` (u = bShift t ⟹ guard genuinely bounded).
Then INTEGRATE: `chSigma1` = `chUniv` + a `!(isSigma1 ℒₒᵣ).sigma/.pi K` conjunct; redo
`InductionSigma1R.defined` (same simp) + `chSigma1_mem_iff` (copy chUniv_mem_iff, add the side
condition via correctness); `delta1_sigma1` mirrors `delta1_univ`.

Below is the drafted code (needs items 1-5 before it compiles):
-/

/-! ## Internal `Σ₁`-formula predicate `IsSigma1` (for `C = Hierarchy 𝚺 1`)

`IsSigma1 p` recognizes codes of `𝚺₁` formulas over `ℒₒᵣ`. By `Hierarchy.sigma₁_induction'`,
a formula is `𝚺₁` iff built from atoms (`=,≠,<,≮,⊤,⊥`) by `∧`, `∨`, (unbounded) `∃`, and **bounded
`∀`** `∀⁰[“#0 < !!(bShift t)”] φ`, whose body desugars to `(^#0 ^≮ u) ^⋎ φ` with `u = termBShift t`.
We assume the input is already a semiformula (the recognizer conjoins `IsSemiformula`), so atoms are
matched purely structurally. Positivity (`u` is a `bShift`-image) is `Δ₁`: `termBShift` only grows
codes, so `∃ t ≤ u, termBShift t = u` is a *bounded* `∃` over the `Δ₁` graph `termBShiftGraph`. -/

section isSigma1

namespace IsSigma1F

/-- The single-step operator: `p` is `𝚺₁` given that its immediate subformulas in `C` are. -/
def Phi (C : Set V) (p : V) : Prop :=
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ k r v, p = ^rel k r v) ∨
  (∃ k r v, p = ^nrel k r v) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∃ p₁) ∨
  (∃ u q, (∃ t, u = termBShift ℒₒᵣ t) ∧ q ∈ C
      ∧ p = qqAll (qqOr (qqNLT (qqBvar 0) u) q))

private lemma phi_iff (C p : V) :
    Phi ℒₒᵣ {x | x ∈ C} p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^nrel k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∃ p₁) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqAll (qqOr (qqNLT (qqBvar 0) u) q)) where
  mp := by
    unfold Phi
    rintro (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, hp, rfl⟩ | ⟨u, q, ⟨t, rfl⟩, hq, rfl⟩)
    · tauto
    · tauto
    · refine Or.inr (Or.inr (Or.inl ⟨k, ?_, r, ?_, v, ?_, rfl⟩)) <;> simp
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨k, ?_, r, ?_, v, ?_, rfl⟩))) <;> simp
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, ?_, p₂, ?_, hp, hq, rfl⟩)))) <;> simp
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, ?_, p₂, ?_, hp, hq, rfl⟩))))) <;> simp
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, ?_, hp, rfl⟩)))))) <;> simp
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, ?_, q, ?_, ⟨t, ?_, rfl⟩, hq, rfl⟩))))))
      · -- u = termBShift t < ^∀ ((^#0 ^≮ u) ^⋎ q): u < ^≮ < ^⋎ < ^∀
        exact lt_trans (lt_qqLT_right _ _) (lt_trans (lt_or_left _ _) (lt_forall _))
      · exact lt_trans (lt_or_right _ _) (lt_forall _)
      · -- t ≤ termBShift t = u, and u < p
        exact lt_of_le_of_lt (le_termBShift ℒₒᵣ t)
          (lt_trans (lt_qqLT_right _ _) (lt_trans (lt_or_left _ _) (lt_forall _)))
  mpr := by
    unfold Phi
    rintro (rfl | rfl | ⟨k, _, r, _, v, _, rfl⟩ | ⟨k, _, r, _, v, _, rfl⟩
      | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, hp, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, rfl⟩, hq, rfl⟩)
    · tauto
    · tauto
    · exact Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, hp, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, q, ⟨t, rfl⟩, hq, rfl⟩))))))

def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExsDef p p₁) ∨
    (∃ u < p, ∃ q < p, ∃ g < p, ∃ bv < p, ∃ nlt < p,
       (∃ t < p, !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C ∧ !qqBvarDef bv 0
       ∧ !qqNLTDef nlt bv u ∧ !qqOrDef g nlt q ∧ !qqAllDef p g)”)
  (.mkPi “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExsDef p p₁) ∨
    (∃ u < p, ∃ q < p, ∃ g < p, ∃ bv < p, ∃ nlt < p,
       (∃ t < p, ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧ q ∈ C ∧ !qqBvarDef bv 0
       ∧ (∀ nlt', !qqNLTDef nlt' bv u → nlt = nlt') ∧ !qqOrDef g nlt q ∧ !qqAllDef p g)”)⟩

def construction : Fixpoint.Construction V (blueprint ℒₒᵣ) where
  Φ := fun _ ↦ Phi ℒₒᵣ
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, (termBShift.defined (L := ℒₒᵣ)).df.iff,
        (qqNLT_defined (V := V)).df.iff]
    · intro v
      symm
      simpa [blueprint, eq_comm, (termBShift.defined (L := ℒₒᵣ)).df.iff,
        (qqNLT_defined (V := V)).df.iff, qqBvar, qqOr, qqAll] using phi_iff ℒₒᵣ _ _
  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, hp, rfl⟩ | ⟨u, q, ht, hq, rfl⟩)
    · tauto
    · tauto
    · tauto
    · tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, hC hp, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, q, ht, hC hq, rfl⟩))))))

instance : (construction ℒₒᵣ).StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, hp, rfl⟩ | ⟨u, q, ht, hq, rfl⟩)
    · tauto
    · tauto
    · tauto
    · tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, ⟨hp, by simp⟩, rfl⟩))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, q, ht, ⟨hq, ?_⟩, rfl⟩))))))
      exact lt_trans (lt_or_right _ _) (lt_forall _)

end IsSigma1F

/-- `IsSigma1 p`: `p` codes a `𝚺₁` formula over `ℒₒᵣ` (assuming `p` is a semiformula). -/
def IsSigma1 (p : V) : Prop := (IsSigma1F.construction ℒₒᵣ).Fixpoint ![] p

/-- Concrete `𝚫₁`-recognizer for `IsSigma1`. -/
noncomputable def isSigma1 : 𝚫₁.Semisentence 1 := (IsSigma1F.blueprint ℒₒᵣ).fixpointDefΔ₁

variable {L}

instance IsSigma1.defined : 𝚫₁-Predicate (IsSigma1 (V := V) ℒₒᵣ) via isSigma1 ℒₒᵣ :=
  (IsSigma1F.construction ℒₒᵣ).fixpoint_definedΔ₁

end isSigma1
