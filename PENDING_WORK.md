# PENDING_WORK — discharging `(InductionScheme ℒₒᵣ C).Δ₁`

Branch `feat/induction-scheme-delta1`. Deliverable: `InductionSchemeDelta1.lean` sorry-free.
Status: scaffold green; `PeanoMinus.delta1` real; `PA`/`IΣ₁` assembled via `Theory.Δ₁.add`.
The **only** open obligations are the two crux instances:

```
InductionScheme.delta1_univ   : (InductionScheme ℒₒᵣ Set.univ).Δ₁
InductionScheme.delta1_sigma1 : (InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)).Δ₁
```

Upstream FFL (origin/master snapshot 2026-04-15) still ships both as `axiom`s — nothing to port.

---

## What `Theory.Δ₁ T` requires (`Bootstrapping/Syntax/Theory.lean:13`)

```
ch       : 𝚫₁.Semisentence 1
mem_iff  : ∀ φ : SyntacticFormula ℒₒᵣ, ℕ ⊧/![⌜φ⌝] ch.val ↔ ∃ σ ∈ T, φ = σ
isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁
```

So we must give an arithmetic Δ₁ formula `ch(p)` true (in ℕ) exactly of codes `p = ⌜σ⌝`
with `σ ∈ InductionScheme ℒₒᵣ C`, i.e. `σ = univCl (succInd ψ)` for some `ψ` with `C ψ`.

`InductionScheme ℒₒᵣ C := { σ | ∃ ψ : Semiformula ℒₒᵣ ℕ 1, C ψ ∧ σ = .univCl (succInd ψ) }`
- `succInd ψ = “!ψ 0 → (∀ x, !ψ x → !ψ (x+1)) → ∀ x, !ψ x”`   (`Arithmetic/Schemata.lean:17`)
- `univCl φ = (∀⁰* (Rew.fixitr 0 φ.fvSup ▹ φ)).toEmpty`        (`Basic/Syntax/Rew.lean:478`)

The painful structural feature: `univCl` prepends a **data-dependent number** (`fvSup ψ`) of
universal quantifiers after rewriting the free vars `&0..&(fvSup-1)` to bound vars (`fixitr`).

---

## Internal primitives ALREADY available (all Σ₁, with correctness + ProperOn)

In `Bootstrapping/Syntax/`:
- constructors (`Formula/Basic.lean`): `qqRel/qqNRel/qqVerum/qqFalsum`, `qqAnd ^⋏`, `qqOr ^⋎`,
  `qqAll ^∀`, `qqExs ^∃` — each **𝚺₀-Function**; term side `qqBvar ^#`, `qqFvar ^&`.
- `IsUFormula` / `IsSemiformula L n p` (`Formula/Basic.lean:268`) — `𝚫₁`, with a `𝚺₁` induction
  principle `IsSemiformula.induction_sigma₁`.
- `bv L p` (`Formula/Basic.lean:1150`) — internal count of bound vars.
- `neg`, `shift`, `subst`/`substs`, `substs1`, `free` (`Formula/Functions.lean`) — all `𝚺₁`-Function
  with full `simp` correctness (`neg_and`, `substs_or`, `shift_substs`, …).
  - `free L p = substs1 L ^&0 (shift L p)`  (binds bvar 0 to fresh fvar) — the *inverse* direction
    of what we need; the closure needs **bound←free** (a `fixitr`-style map), see GAP below.
- `qqConj`, `qqDisj`, `substItr` (`Formula/Iteration.lean`) — `𝚺₁` iterators (template for new ones).
- coding bridges (`Formula/Coding.lean`): `⌜·⌝`, `quote_all : ⌜∀⁰ φ⌝ = ^∀ ⌜φ⌝`, `quote_and`, …,
  `quote_isSemiformula*`. Typed layer `Bootstrapping.Semiformula V L n` with `typed_quote_*` simp.

## THE GAP — UPDATE (lap 2026-06-22)

**Part (a) — iterated-∀ — DONE, sorry-free** in `InductionSchemeDelta1.lean`:
`qqAlls p k = ^∀^[k] p` (Σ₁, `qqAllsDef`), with `qqAlls_all`, `qqAlls_succ'`, `le_qqAlls`,
`isUFormula_qqAlls`, `bv_qqAlls`, `IsSemiformula.qqAlls`, and the headline
`quote_allClosure : ⌜∀⁰* φ⌝ = qqAlls ⌜φ⌝ n`.

**Part (b) — free↔bound — the remaining hard piece. KEY: DECODE avoids building `fixitr`.**
`univCl' (succInd ψ) = ∀⁰* (fixitr 0 m ▹ succInd ψ)`, `m = fvSup ψ`. The body
`b := fixitr 0 m ▹ succInd ψ` has these meta properties (`Basic/Syntax/Rew.lean`):
- `b` is **freevar-free** with `m` bound slots (`not_fvar?_fixitr_fvSup`), i.e. internally
  `IsSemiformula ℒₒᵣ m b ∧ shift b = b` (= `IsFVFree m b`, already Σ₁: `isFVFreeDef`).
- `subst_comp_fixitr : b ⇜ (fun i ↦ &i) = succInd ψ`  ⇒ the closure is **invertible** by
  substituting the `m` bound vars with the free-var atoms `&0..&(m-1)`.

⇒ Recognizer (DECODE) reuses the **already-proven internal `subst`** instead of a new `fixitr`:
`ch(p) := ∃ m ≤ p, ∃ b ≤ p, p = qqAlls b m ∧ IsFVFree ℒₒᵣ m b ∧`
`  succIndShape (subst (fvarVec m) b) ∧ Cᵢ(ψ-of-that-shape)`
where `fvarVec m = ⟨^&0, …, ^&(m-1)⟩` (a small new Σ₁ vector fn, template `repeatVec`), and
`subst (fvarVec m) b` is the internal `b⇜(&·)`. Then `succIndShape` decodes the `succInd`
structure (top `^⋎`/`imp` tree → recover `q`, check `b0 = q[0]`, step `= q[#0+1]`, concl `^∀ q`).
mem_iff: forward via `quote_allClosure` + `subst_comp_fixitr`; uniqueness of `m=fvSup` is
automatic because `qqAlls`+`IsFVFree` only matches the canonical closure.

This is still real work (`fvarVec`, `succIndShape`/decode, the side condition, mem_iff, ProperOn)
but it **removes the need to build `fixitr` internally** — the single biggest risk. Build `fvarVec`
and `succIndShape` next (both self-contained, template-able), then assemble.

(Old note: no internal universal-closure/`fixitr`/iterated-∀ existed; (a) now built, (b) decoded.)

---

## ⭐ REFINED RECOGNIZER (lap 2026-06-22b) — no internal `fvSup`/`fixitr` needed

Two facts changed the plan:
1. **`!φ t` in formula position is `φ ⇜ ![t]` (`Rew.substs`), NOT `embSubsts`** (BinderNotation.lean:419).
   So `⌜succInd φ⌝` decomposes via the EXISTING `typed_quote_substs`. Verified:
   `typed_quote_succInd` (in deliverable). The handoff's `typed_quote_embSubsts` task is VOID.
   `succInd φ = (φ⇜![‘0’]) 🡒 ((∀⁰(φ 🡒 φ⇜![‘#0+1’])) 🡒 ∀⁰φ)` (`succInd_eq`, verified).
2. **DECODE needs neither internal `fvSup` nor internal `fixitr`** — closure inversion is the proven
   internal `subst`, and `m=fvSup` is pinned by the internal `bv` count, not a new function.

Verified bridge lemmas now in `InductionSchemeDelta1.lean` (all sorry-free, axiom-clean):
- `quote_univCl_eq : ⌜univCl ψ⌝ = qqAlls ⌜fixitr 0 (fvSup ψ) ▹ ψ⌝ (0 + fvSup ψ)`.
- `quote_subst_fvar_fixitr : ⌜(fixitr 0 (fvSup ψ) ▹ ψ) ⇜ (&·)⌝ = ⌜ψ⌝`  (closure inversion).
- `typed_quote_succInd`, `succInd_eq`.

**The recognizer (C = Set.univ):**
```
ch(p) := ∃ m ≤ p, ∃ b ≤ p, ∃ K ≤ p,
   p = qqAlls b m                            -- p is the m-fold ^∀ of b
 ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b        -- b is freevar-free (IsFVFree)
 ∧ bv ℒₒᵣ b = m                              -- PINS m = fvSup(succInd ψ): forbids unused leading ∀
 ∧ IsSemiformula ℒₒᵣ 1 K                     -- K = ⌜ψ⌝, ψ : Semiformula ℒₒᵣ ℕ 1
 ∧ subst (fvarVec m) b = indBody K           -- recover ⌜succInd ψ⌝ from b; check succInd shape
 ∧ Cᵢ K                                      -- side condition (⊤ for univ)
```
where:
- `fvarVec m := ![^&0, …, ^&(m-1)]` — small new Σ₁ vector fn (template `repeatVec`/`Vec`); at the
  *typed* layer it is literally `fun x ↦ ^&x`, so `subst (fvarVec m) b` = the meta `b ⇜ (&·)`.
- `indBody K := (K.subst ![⌜0⌝]) 🡒 ((∀⁰ (K 🡒 K.subst ![⌜#0+1⌝])) 🡒 ∀⁰ K)` — a TYPED-layer composite
  of `subst`/`🡒`/`∀⁰` (all Σ₀/Σ₁-definable). `indBody ⌜ψ⌝ = ⌜succInd ψ⌝` is exactly `typed_quote_succInd`.

**Why `bv b = m` pins `m = fvSup`** (no over-recognition by padding leading ∀): `IsUFormula b ∧
shift b = b ∧ bv b = m` ⇒ `b ⇜ (&·)` has its free vars exactly `&0..&(m-1)` with `&(m-1)` occurring,
so `fvSup(b ⇜ (&·)) = m`; combined with `subst(fvarVec m) b = ⌜succInd ψ⌝` and the bijection
`{FV-free, bv=m} ≅ {fvSup=m}` (inverse `fixitr`), `b = fixitr 0 m ▹ succInd ψ`, `m = fvSup`. So
`p = qqAlls b m = ⌜univCl(succInd ψ)⌝` exactly. (Needs meta lemma `bv(fixitr 0 (fvSup) ▹ χ)=fvSup`
for the forward dir — i.e. `&(fvSup-1)` occurs; "sup attained", from `fvSup`/`freeVariables` defs.)

**Remaining build (in order):**
- ✅ DONE `fvarVec : V → V` (Σ₁ vector of `^&0..^&(m-1)`): `fvarVec_zero/succ`, `fvarVecDef`+`𝚺₁-Function₁`,
  `len_fvarVec`, `nth_fvarVec`, `fvarVec_val_eq`, **`subst_fvarVec_quote`** (raw closure inversion).
- ✅ DONE `indBody` typed + `indBody_quote : indBody ⌜ψ⌝ = ⌜succInd ψ⌝`. (Raw `.val` Σ₁-graph still TODO
  for assembly — extract `indBody.val : V → V` as a definable function.)
- ✅ DONE (lap 2026-06-22 late) ⭐ **`bv_quote_fixitr : bv (V:=ℕ) ⌜fixitr 0 (fvSup χ) ▹ χ⌝ = fvSup χ`**
  — the pin, axiom-clean. Proven by level-factoring (`IsSemiformula.sound` + `subst_comp_fixitr`), NO meta
  `bvSup` needed. Supporting (also DONE, axiom-clean): `Semiterm/Semiformula.quote_castLE`,
  `.freeVariables_castLE`. V=ℕ cast/order soup handled via `natCast_nat` (model cast on ℕ = id) and the
  fact model `<` on ℕ = `Nat.lt` (so `omega` works after `simp only [natCast_nat]` + unfolding the model
  `≤` def `= ∨ <`). REUSE THESE for the mem_iff ℕ-casts.
- ⬜ extract `indBodyGraph`/Σ₁-graph of `indBody.val`; internal Δ₁ assembly of `ch` via
  `HierarchySymbol.Semiformula` combinators (`bex`/`and`/graph-eq), proving `DefinedPred (V:=V) R ch`
  → `ProperOn` is FREE (`Defined.proper`). (Infra validated by `qqAllsDef`/`fvarVecDef` patterns; for the
  blueprint style mirror `bv.blueprint`/`isSemiformula` `.mkSigma/.mkPi` with the `…Def`/`…Graph` of each
  internal op.) ← **NEXT: this is the main remaining grind.**
- ⬜ `mem_iff` over ℕ. **Forward** (member ⟹ recognizer): all bridges in place — `quote_univCl_eq`
  (p = qqAlls b m, m=0+fvSup), `subst_fvarVec_quote` (subst recovers ⌜succInd ψ⌝), `indBody_quote`,
  and now `bv_quote_fixitr` to verify the `bv b = m` clause. **Backward**: from `bv b = m` + freevar-free,
  `IsSemiformula.sound` gives γ; `bv_quote_fixitr` pins `m = fvSup`; `quote_univCl_eq` closes
  `p = ⌜univCl(succInd ψ)⌝`. (Same level-factoring as inside `bv_quote_fixitr`.)
- ⬜ `isDelta1 := ProvablyProperOn.ofProperOn _ (fun V _ _ ↦ Defined.proper)`.
- ⬜ Pkg into `Theory.Δ₁` record; `delta1_univ`. Then `C=Hierarchy 𝚺 1`: add internal Σ₁-formula pred for `Cᵢ`.

**Recognizer R(p) (C = univ), the bv-pin clause now justified:**
```
R(p) := ∃ m ≤ p, ∃ b ≤ p, ∃ K ≤ p,
   p = qqAlls b m  ∧  IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b  ∧  bv ℒₒᵣ b = m
 ∧ IsSemiformula ℒₒᵣ 1 K  ∧  subst (fvarVec m) b = (indBody K).val
```
`bv b = m` is sound by `bv_quote_fixitr` (member: b=⌜fixitr 0 (fvSup) ▹ succInd ψ⌝ has bv = fvSup = m;
over-recog with m'>fvSup is rejected since bv b' = fvSup < m'). For `C = Hierarchy 𝚺 1`: add `Cᵢ K`.

**KEY infra fact:** `Theory.Δ₁.ch` needs a CONCRETE `𝚫₁.Semisentence 1`; `Definable` is a `Prop`
(formula not extractable). So `ch` must be built explicitly with combinators and a `Defined R ch`
proof (template: `qqAllsDef`, or `IsSemiformula`/`Derivation.defined`). `Defined` (Δ-[m]) CARRIES
`ProperOn V` (Definable.lean:186) ⇒ no separate ProperOn grind.

---

## Recognizer design (OLD — RECONSTRUCT; superseded by REFINED above, kept for reference)

`ch(p) := ∃ q ≤ p, IsSemiformula ℒₒᵣ 1 q ∧ Cᵢ(q) ∧ inductionAxiom(q) = p`

where `inductionAxiom : V → V` is a new **Σ₁** function with the correctness theorem
`inductionAxiom ⌜ψ⌝ = ⌜univCl (succInd ψ)⌝`  (ψ : Semiformula ℒₒᵣ ℕ 1).
Δ₁-ness then follows: bounded `∃q≤p` over a Σ₁-graph equality is Σ₁; the matching Π₁ form
(`∀q≤p, … → p = …` already determines `q`) gives Δ₁ via `HierarchySymbol.…mkDelta`, mirroring
`formulaAux`/`isUFormula` in `Formula/Basic.lean`.

Pieces:
- **P1 (core).** `inductionAxiom` + correctness. Decompose:
  - `succIndCode q := impl (substTop ‘0’ q) (impl (^∀ (impl q (substTop ‘#0+1’ q))) (^∀ q))`
    using `substs1` for the `0`/`x+1` instances and `qqAll`, with `impl a b := neg a ^⋎ b`.
    Correctness from the `substs_*`/`neg_*` simp set + `quote_*`. (Moderate; primitives exist.)
  - `uclose q := ^∀^[fvSup q] (fixitrCode (fvSup q) q)` — **the GAP**. Need:
    (i) internal `fvSup` (max fvar index +1) — a `𝚺₁` recursion over the formula code;
    (ii) internal `fixitr k` (rewrite `^&i ↦ ^#(i+offset)`, shift existing bvars) — a `𝚺₁`
         recursion (template: the `neg`/`shift` UformulaRec constructions);
    (iii) iterated `^∀` — a trivial `𝚺₁` PR recursion on `fvSup q` (template: `qqConj`).
    Correctness `uclose ⌜χ⌝ = ⌜univCl χ⌝` by `IsSemiformula` induction + `quote_all`.
- **P2 (bound).** `q ≤ inductionAxiom q` (so `∃q≤p` is sound). Follows from code-size monotonicity
  of the `qq*` pairing (`nth_lt_qqRel_of_lt` style) — `succIndCode`/`uclose` only grow the code.
- **P3 (side condition `Cᵢ`).**
  - `C = Set.univ`: `Cᵢ(q) := ⊤`. **Do this case first** → clears `PA_delta1Definable`.
  - `C = Hierarchy 𝚺 1`: need internal "`q` is a Σ₁ formula" predicate. Likely another arithmetized
    recursion (Σ₁ = ∃-prenex over Δ₀); search for any existing `Hierarchy`/`isSigma` arithmetization
    before building. Clears `ISigma1_delta1Definable`.
- **P4 (packaging).** Assemble `ch` as `𝚫₁.Semisentence 1`, discharge `mem_iff` (transfer ℕ-eval of
  the bounded-∃ to the set condition via `inductionAxiom` correctness + `quote_inj`), and
  `isDelta1`/`ProvablyProperOn` (the Σ/Π forms agree — standard for graph-of-function recognizers;
  model on `Δ₁Class.defined`).

### Alternative: DECODE (avoid building `uclose`)
`ch(p)` strips the leading `^∀`-block (count `k`), asserts the body has the `succInd` shape
`b0 ^→ (^∀(c ^→ c')) ^→ ^∀ c`, recovers `ψ`-body `c`, checks `b0 = c[0]`, `c' = c[#0+1]`, `Cᵢ(c)`,
**and** that `k` equals the closure arity so only the canonical `univCl` normal form is accepted
(the equality-to-normal-form check re-introduces ~the same `fixitr` reasoning). Comparable cost;
RECONSTRUCT keeps a clean functional correctness lemma, so prefer it.

---

## Attack paths (per the unblock protocol)

**Path A — RECONSTRUCT, univ-first (recommended).**
1. Build `succIndCode` + correctness (no closure needed yet); unit-test on a closed ψ.
2. Build the three closure helpers (`fvSup`, `fixitrCode`, iterated-∀) one at a time, each Σ₁
   with a `quote_*` correctness lemma proven by `IsSemiformula` induction.
3. Assemble `inductionAxiom`, prove P1 correctness, P2 bound.
4. Package `ch` with `Cᵢ = ⊤`; finish `delta1_univ`; delete dependence → `PA_delta1Definable` real.
5. Add internal Σ₁-predicate (P3b); `delta1_sigma1`.

**Path B — DECODE.** Skip `uclose`; recognize structurally (see Alternative). Use if the
free→bound `fixitr` recursion proves nastier than a normal-form equality check.

**Path C — minimize the closure.** Prove a meta lemma `univCl (succInd ψ) = succInd ψ` is FALSE in
general (params), but the *image* `inductionAxiom` may be expressible via existing `free`/`shift`
adjunctions: investigate whether `univCl χ`'s code equals `^∀^[bv] (iterate free⁻¹ …)` reusing
`shift`/`free` instead of a fresh `fixitr` — could reuse proven `shift_substs`/`free` lemmas and
cut new-recursion work. Scout `shift`/`free` interaction with `^∀` before committing.

## KEY INSIGHT — build at the TYPED layer (`Bootstrapping.Semiformula V L n`)

`Formula/Typed.lean` wraps raw codes as `Semiformula V L n` (a `{val // IsSemiformula …}`) with
typed constructors `all (∀⁰)`, `arrow (🡒 = imp)`, `subst`, `shift`, full `LogicalConnective`.
Crucially `⌜·⌝ : SyntacticSemiformula L n → Bootstrapping.Semiformula V L n` is an
`LCWQIsoGödelQuote` homomorphism: `Coding.lean` gives `typed_quote_substs`, `typed_quote_shift`,
`typed_quote_all`(via `quote_all`), `⌜φ 🡒 ψ⌝ = ⌜φ⌝ 🡒 ⌜ψ⌝`, etc. as `@[simp]`.

⇒ Define `inductionAxiom` at the **typed** layer; its correctness
`⌜univCl (succInd ψ)⌝ = inductionAxiomTyped ⌜ψ⌝` then collapses under the `typed_quote_*` simp set,
EXCEPT the closure step (still needs a typed `fixitr`/iterated-`all`). Extract the raw Σ₁ `.val`
function + graph afterwards (pattern: `Functions.lean` `neg`/`subst` expose `…Graph` + `defined`).
This removes almost all hand-rolled raw-code reasoning from P1; only THE GAP (closure) stays hard.

Concretely `succIndTyped (q : Semiformula V ℒₒᵣ 1) :=`
`(q.subst ![0]) 🡒 ((∀⁰ (q 🡒 q.subst ![#0+1])) 🡒 ∀⁰ q)`  — all typed ops, correctness by `simp`.

## Notes
- Aristotle is a poor fit here (mathlib-tuned; this API is Foundation-bespoke). Keep local.
- Win condition: `#print axioms PA_delta1Definable` / `ISigma1_delta1Definable` =
  `[propext, Classical.choice, Quot.sound]`. Never close with a new `axiom`/`sorry`.

---

## ⭐ LAP 2026-06-23b — ch ASSEMBLY DONE; PA reduced to 2 obligations

The entire recognizer is built + verified. `delta1_univ` compiles; only `chUniv_mem_iff`'s
two hard sub-steps + the IΣ₁ predicate remain. Build green, 3 sorries.

**DONE (axiom-clean, committed):** `indBodyValGraph`(+via), `chUniv`(𝚫₁.Semisentence), 
`InductionUnivR.defined`, `delta1_univ`(ch/isDelta1/mem_iff wired), `chUniv_mem_iff` 
backward 5/6 clauses + shift + subst, forward fully structured, `shift-fix` lemma, 
`indBodyVal_quote`, `mem_inductionScheme_univ_iff`.

**REMAINING (3 sorries in InductionSchemeDelta1.lean):**

1. **`closure_inversion`** (forward keystone). COMPLETE PROOF PATH FOUND:
   - (*) `β = Rew.fixitr 0 m ▹ χ` (χ=succInd γ) via `rew_eq_self_of` on composite
     `(fixitr 0 m).comp (subst (fun i:Fin m ↦ &↑i))` = id on β (β freevar-free, #x↦#x); uses hβγ.
   - (A) `m = χ.fvSup`: `fixitr 0 m ▹ χ = castLE h ▹ (fixitr 0 χ.fvSup ▹ χ)` (agree on χ's fvars),
     so `⌜fixitr 0 m ▹ χ⌝ = ⌜fixitr 0 χ.fvSup ▹ χ⌝` by `Semiformula.quote_castLE` (code-preserving),
     hence `bv ⌜β⌝ = bv ⌜fixitr 0 χ.fvSup ▹ χ⌝ = χ.fvSup` (bv_quote_fixitr); with hbv ⟹ m = χ.fvSup.
   - conclude: `χ.univCl' = ∀⁰* (fixitr 0 χ.fvSup ▹ χ) = ∀⁰* β` (transport over m = χ.fvSup; HEq/cast fiddle).
   ALL prerequisite lemmas exist in-file. Est ~0.5-1 lap (dependent-type casts).

2. **`⌜ψ⌝ ≤ ⌜univCl'(succInd ψ)⌝`** (backward K≤p bound). `⌜ψ⌝ ≤ indBodyVal ⌜ψ⌝` is clean
   (ψ appears as `qqAll ⌜ψ⌝` inside; lt_qqAll). Then need `subst(fvarVec m) b ≤ qqAlls b m`
   OR `⌜succInd ψ⌝ ≤ ⌜univCl'⌝` — a code-size lemma through fixitr (NEW). Est ~0.5-1 lap.

3. **`delta1_sigma1`** (IΣ₁). Reuse univ recognizer + internal "ψ is Σ₁" predicate Cᵢ.
   Search Arithmetic/Hierarchy arithmetization first. Est ~1-2 laps.

---

## ⭐⭐ LAP 2026-06-23c — closure_inversion PROVEN; PA gated on ONE code-size bound

**HUGE progress.** `chUniv_mem_iff` forward direction is **fully proven** (`closure_inversion`
done — the hard keystone). PA.Δ₁ now has **exactly ONE** remaining obligation + the separate IΣ₁ piece.

**`closure_inversion` proof (DONE, in-file):** work at CODE level (`⌜·⌝:ℕ` erases level index,
sidestepping `0+m` vs `m` casts). `⌜fixitr 0 m ▹ χ⌝ = ⌜β⌝` via rebind composite = `castLE` on β
(`rew_eq_of_funEqOn`, β freevar-free). Then `m = χ.fvSup` via `castLE` code-preservation
(`quote_castLE`) + `bv_quote_fixitr`. Conclude via `quote_allClosure` + `quote_inj`.

**REMAINING for PA (1 sorry, line ~771): the K≤p code bound.**
Goal: `⌜ψ⌝ ≤ ⌜univCl'(succInd ψ)⌝` over ℕ (= `qqAlls b (0+χ.fvSup)`, χ=succInd ψ, b=⌜fixitr 0 fvSup ▹ χ⌝).
- `⌜ψ⌝ ≤ ⌜succInd ψ⌝` is CLEAN: `succInd_eq` shows `∀x !ψ x = ∀⁰ ψ` (identity subst), so
  `^∀ ⌜ψ⌝ = ⌜∀⁰ ψ⌝` is a literal subformula → `⌜ψ⌝ ≤ ^∀ ⌜ψ⌝ ≤ ⌜succInd ψ⌝` via `le_qqAll` + imp/qqOr
  containment lemmas (`le_qqAll` exists; need `q ≤ imp p q` i.e. right-arg of qqOr — search `le_qqOr`).
- The HARD half: `⌜succInd ψ⌝ ≤ ⌜univCl'(succInd ψ)⌝`. KEY FINDING: `^#z = ⟪0,z⟫+1 < ⟪1,z⟫+1 = ^&z`
  (qqBvar < qqFvar). So `fixitr` (free→bound) SHRINKS leaf codes ⟹ `⌜fixitr▹χ⌝ ≤ ⌜χ⌝`, while
  `subst(fvarVec)` (bound→free) GROWS them. So `⌜χ⌝ ≤ b` is FALSE and `⌜χ⌝ ≤ qqAlls b fvSup` is a
  genuine size-RACE: the `fvSup` ∀-wrappers (each ~doubles via pairing) must dominate the leaf
  shrink. True (esp. fvSup≥1 blows up exponentially; fvSup=0 ⟹ univCl'=χ so equality), but needs
  real code-size lemmas. **Attack paths:** (a) prove `⌜χ⌝ ≤ qqAlls b k` by induction on k with a
  per-∀ growth lemma `x ≤ ^∀ x` (le_qqAll) + base `⌜χ⌝ ≤ b` when fvSup=0 (then χ closed, fixitr=id,
  b=⌜χ⌝); the fvSup≥1 case needs `⌜χ⌝ ≤ ^∀ b` — compare `⌜χ⌝` vs `⌜fixitr▹χ⌝` leaf-by-leaf +
  one pairing layer. (b) prove a meta `encode`-monotonicity `encode χ ≤ encode (univCl' χ)` via the
  pairing structure. (c) RECOGNIZER REDESIGN: none found that dodges it (K≤p, K≤b, K≤s all hit the
  same `⌜χ⌝ ≤ p` wall; s=subst image isn't a polynomial DSL bound term).

**Then IΣ₁ (line ~817 `delta1_sigma1`):** univ recognizer + internal "ψ is Σ₁" predicate Cᵢ.

**K-bound instance note (next lap):** the `K ≤ p` goal uses the *model* `≤` over ℕ
(`instLE_foundation`, = `⟪=∨<⟫`), NOT `Nat.le`. The clean half (`⌜ψ⌝ ≤ ⌜succInd ψ⌝`) is one line —
`(le_qqAll _).trans ((lt_or_right _ _).le.trans (lt_or_right _ _).le)` after
`rw [hχ, ← indBodyVal_quote ψ]; unfold indBodyVal Bootstrapping.imp` — BUT do NOT write explicit
`have _ : (⌜ψ⌝:ℕ) ≤ _` annotations (they resolve to `Nat.le` and clash with the foundation `≤` from
`le_qqAll`). Build the term from the foundation lemmas directly, or convert the goal to `Nat.le`
first via the PeanoMinus ℕ-order bridge. The hard half (`⌜χ⌝ ≤ ⌜χ.univCl'⌝`, the size race) inlines
as a foundation-`≤` `sorry` cleanly since it inherits the goal instance.

---

## ⭐⭐⭐ LAP 2026-06-23d — PA_delta1Definable PROVEN axiom-clean; size race DISSOLVED

**The size race never had to be fought.** Restructured `chUniv` so the recovered core `K` is
bounded by the functionally-pinned `subst (fvarVec m) b` (call it `s`) instead of by the input `p`.
- `s` is already an *unbounded-but-functional* existential in the recognizer (`∃ s, substsGraph s fv b`),
  so the Π-form stays Π₁ by keeping `indBodyVal` in functional form `∀ ib, indBodyValGraph ib K → s = ib`.
- Backward obligation flips from `⌜ψ⌝ ≤ p` (the combinatorial code-size race through fixitr/∀-closure,
  which was TRUE but a multi-lap Nat-pairing nightmare with leaf-shrink amplification) to
  `⌜ψ⌝ ≤ indBodyVal ⌜ψ⌝ = ⌜succInd ψ⌝` — the **clean half**, proven by new lemma `le_indBodyVal`
  (`k ≤ indBodyVal k`: the core is the bound body of the `^∀ K` conclusion inside the succInd shape,
  via `le_qqAll` + two `lt_or_right`). NOTE the `<`→`≤` cast: do it inside a *generic-V* helper
  lemma (`le_indBodyVal`) so the ORingStructure/Preorder LT diamond resolves; the `.le`/`le_of_lt`
  dot-notation diamonds out at `V = ℕ` (foundation `≤` vs Nat.le).
- `InductionUnivR.defined` carried the reorder under the SAME `simp` (no change).
- `#print axioms PA_delta1Definable = [propext, Classical.choice, Quot.sound]`. ✅ B2 DONE.

**ONLY delta1_sigma1 (IΣ₁, line ~831) remains** — the deep arithmetization.

### IΣ₁ blueprint (verified building blocks; this is the from-scratch internal Σ₁-formula predicate)

**Characterization (CONFIRMED by `Hierarchy.sigma₁_induction'`, Arithmetic/Basic/Hierarchy.lean:458):**
over ℒₒᵣ, `Hierarchy 𝚺 1 ψ` ⟺ ψ is built from atoms (`=,≠,<,≮,⊤,⊥`) by `∧`, `∨`,
**bounded ∀** `∀⁰[“#0 < !!(Rew.bShift t)”] φ`, and (unbounded) `∃`. Formulas are NNF (no raw ¬),
so "every ∀ is bounded" is syntactically visible. The bounded-∀ body desugars to
`qqOr (qqNLT (qqBvar 0) u) inner` with `u = termBShift t` (positivity = bShift-image, has no #0).

**Define `isSigma1 : V → Prop` as a `Fixpoint.Blueprint 0`** (template: `FormalizedFormula` in
`Formula/Basic.lean:201-282` — `formulaAux`/`blueprint`/`construction`/`StrongFinite`/`fixpointDefΔ₁`).
The `Phi` clauses (mirror `phi_iff`):
```
Phi C p :=
  p = ^⊤ ∨ p = ^⊥
  ∨ (∃ k<p,∃ r<p,∃ v<p, IsRel k r ∧ IsUTermVec k v ∧ p = ^rel k r v)      -- atoms
  ∨ (∃ k<p,∃ r<p,∃ v<p, IsRel k r ∧ IsUTermVec k v ∧ p = ^nrel k r v)
  ∨ (∃ p₁<p,∃ p₂<p, p₁∈C ∧ p₂∈C ∧ p = p₁ ^⋏ p₂)
  ∨ (∃ p₁<p,∃ p₂<p, p₁∈C ∧ p₂∈C ∧ p = p₁ ^⋎ p₂)
  ∨ (∃ p₁<p, p₁∈C ∧ p = ^∃ p₁)                                            -- unbounded ∃
  ∨ (∃ u<p,∃ inner<p, (∃ t<u, termBShift t = u) ∧ inner∈C                 -- bounded ∀
       ∧ p = ^∀ (qqOr (qqNLT (qqBvar 0) u) inner))
```
All pieces exist & are Σ₁/Σ₀-definable: `termBShiftGraph` (Term/Functions.lean:322),
`qqNLT`/`qqNLTDef`? (Formula/Functions.lean:1200 — check it has a Def; qqLTDef exists at 1240,
qqNLT likely analogous), `qqBvar`/qqBvarDef (Term/Basic.lean:14), `qqOrDef`, `qqAllDef`, `qqExsDef`,
`isRel`, `isUTermVec`. `Δ₁`-ness is FREE from `blueprint.fixpointDefΔ₁` + `construction.fixpoint_definedΔ₁`.

**Correctness `isSigma1 ⌜ψ⌝ ↔ Hierarchy 𝚺 1 ψ`** (over V=ℕ, the recognizer side condition):
- (⟸) `Hierarchy 𝚺 1 ψ → isSigma1 ⌜ψ⌝`: induct with `sigma₁_induction'`; each case emits the matching
  `Phi` clause. Bounded-∀ case: `u = ⌜bShift t⌝ = termBShift ⌜t⌝` (need `termBShift_quote`), and
  `⌜∀⁰[“#0<bShift t”]φ⌝ = ^∀ (qqOr (qqNLT (qqBvar 0) ⌜bShift t⌝) ⌜φ⌝)` via the typed quote simp set.
- (⟹) `isSigma1 ⌜ψ⌝ → Hierarchy 𝚺 1 ψ`: `IsSemiformula.sigma1_structural_induction` (Basic.lean:1352)
  on the code, invert each `Phi` clause to a real subformula + apply the Hierarchy constructor. The
  bounded-∀ clause inversion: `u = termBShift t` ⟹ the guard is a genuine bShift ⟹ `ball` applies
  with positivity from `Rew.positive_iff`/`termBShift` image.

**Integration:** add `Cᵢ K := isSigma1 K` clause to a `chSigma1` recognizer (copy `chUniv` + one
conjunct in both Σ/Π DSL forms + the `isSigma1.sigma`/`.pi` graphs), redo `InductionSigma1R.defined`
(same simp), and `chSigma1_mem_iff` (copy `chUniv_mem_iff`; forward adds `Hierarchy 𝚺 1 γ` from
`isSigma1 K` via correctness ⟹ membership in `InductionScheme ℒₒᵣ (Hierarchy 𝚺 1)`; backward adds
proving `isSigma1 ⌜ψ⌝` from `Hierarchy 𝚺 1 ψ`). Then `delta1_sigma1` mirrors `delta1_univ`.
Est: ~2-3 laps (fixpoint+correctness is the bulk; integration is mechanical copy of the univ case).

### IΣ₁ — positivity check is Δ₁ (resolved obstacle)

The bounded-∀ guard needs "u is the bShift of some term" (= `t.Positive`, no #0). This is **Δ₁**:
`termBShift` only GROWS codes (^#z→^#(z+1) grows; ^&x fixed; ^func recurses), so `termBShift t ≥ t`,
hence any preimage `t ≤ u`. So "u ∈ image" = `∃ t ≤ u, termBShift t = u` — a BOUNDED ∃ over the
Δ₁ function-graph `termBShiftGraph`. In the fixpoint `core` (mkDelta σ/π):
- σ: `∃ t < u+1, !termBShiftGraph u t`
- π: `∃ t < u+1, ∀ u', !termBShiftGraph u' t → u = u'`  (bounded-∃ of Π₁ = Π₁)
NO new "is-positive" recursion needed. Every piece of the isSigma1 fixpoint is now confirmed buildable;
remaining work is intricate DSL + the two correctness inductions + recognizer integration (~2-3 laps).
