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

## THE GAP (the one missing primitive)

No internal **universal-closure / free→bound (`fixitr`) / iterated-∀** function exists.
There is no `quote_univCl` lemma either. This is the heart of the build.

---

## Recognizer design (recommended: RECONSTRUCT)

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
