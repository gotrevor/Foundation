# DIRECTION — discharge Foundation's Δ₁-definability axioms

This worktree (`feat/induction-scheme-delta1`) has **one job**: replace Foundation's two
**axioms** with real proofs, burning them out of `#print axioms` everywhere downstream.

## The target 🎯

In `Foundation/FirstOrder/Incompleteness/Examples.lean`:

```lean
axiom ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁     -- line 15  (TODO, line 10)
axiom PA_delta1Definable      : 𝗣𝗔.Δ₁      -- line 17
```

These are a **disclosed Foundation TODO** ("Prove `𝗜𝚺₁` and `𝗣𝗔` are Δ₁-definable"). Gödel I/II
for the standard theories, and anything chaining through them (including a downstream Goodstein
independence proof), carry these axioms. **Replace each `axiom` with a proven `instance`/theorem
of the same type.** When done, `#print axioms PA_delta1Definable` (now a real decl) must be
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `axiom`.

## The route (decomposition — grounded, the combinators all exist)

```
𝗣𝗔  = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ              (Schemata.lean:52)
𝗜𝚺₁ = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ (Arithmetic.Hierarchy 𝚺 1)
```

`Theory.Δ₁` (`Bootstrapping/Syntax/Theory.lean`) already has, PROVEN:
- `Theory.Δ₁.ofFinite (h : Set.Finite T) : T.Δ₁`
- `Theory.Δ₁.add (dT : T.Δ₁) (dU : U.Δ₁) : (T + U).Δ₁`
- `Theory.Δ₁.ofEq`, `.singleton`, `.empty`, `.insert`, `.ofList`

So:
1. **`𝗣𝗔⁻.Δ₁`** = `ofFinite` + `Set.Finite (𝗣𝗔⁻ : Theory ℒₒᵣ)`. `PeanoMinus` is a finite inductive
   (`PeanoMinus/Basic.lean:35`, ~17 constructors) — enumerate them to get `Set.Finite`. **Easy.**
2. Glue with `add` + `ofEq`. **Trivial.**
3. **THE one real obligation: `(InductionScheme ℒₒᵣ C).Δ₁`** for `C = Set.univ` and
   `C = Arithmetic.Hierarchy 𝚺 1`. Everything else is plumbing around this.

## The crux: `(InductionScheme ℒₒᵣ C).Δ₁`

Provide `ch : 𝚫₁.Semisentence 1` with
`mem_iff : ∀ φ : SyntacticFormula ℒₒᵣ, ℕ ⊧/![⌜φ⌝] ch.val ↔ ∃ σ ∈ InductionScheme ℒₒᵣ C, φ = σ`
and `isDelta1`. Build `ch` as: **"`⌜φ⌝` is the code of the induction axiom `Ind_ψ` of some
formula ψ (with `C ψ`)"**, where
`Ind_ψ := ψ(0) ⋏ (∀x. ψ(x) ⟶ ψ(x+1)) ⟶ ∀x. ψ(x)`.

Tools to build/recognize this internally (all in `Bootstrapping/Syntax/`):
- `Formula/Basic.lean` — `qqAnd`, `qqAll`, `qqRel`, … the internal constructors; each is
  **`𝚺₀`-definable** (`qqAnd_defined : 𝚺₀-Function₂`, `qqAll_defined : 𝚺₀-Function₁`). Composing
  them to form `⌜Ind_ψ⌝` from `⌜ψ⌝` stays Δ₁.
- `Formula/Functions.lean`, `Formula/Iteration.lean`, `Formula/Coding.lean` — substitution
  (`ψ(0)`, `ψ(x+1)`), `IsSemiformula`, free-variable + Gödel-coding predicates.
- Membership is a **bounded** `∃ψ` (the code of `ψ` is `< ` the code of `Ind_ψ`), so
  `∃ψ ≤ n, n = ⌜Ind_ψ⌝ ∧ IsSemiformula ψ ∧ C-cond(ψ)` is Δ₁.
- For `C = Set.univ`: the side condition is `True` — easiest; **do this first** (clears
  `PA_delta1Definable`). For `C = Hierarchy 𝚺 1`: the side condition is "ψ is Σ₁", which needs the
  internal **hierarchy-membership** predicate (search the arithmetized `Hierarchy`/`𝚺`-class
  machinery; it should already be Δ₁-definable). Clears `ISigma1_delta1Definable`.

Likely sub-target if it stalls: confirm internal **substitution** is exposed at the Σ₁/Δ₁ level
(for `ψ(0)`/`ψ(x+1)`); if not, that lemma is the first thing to build. Canonical math reference if
needed: **Hájek–Pudlák, _Metamathematics of First-Order Arithmetic_** (Δ₁-axiomatization of PA) —
request via `ON-LINE-REQUEST.md` (you are offline).

## Milestones
- **B1** `Set.Finite 𝗣𝗔⁻` → `𝗣𝗔⁻.Δ₁`.
- **B2** `(InductionScheme ℒₒᵣ Set.univ).Δ₁` → assemble `𝗣𝗔.Δ₁` → **delete `axiom PA_delta1Definable`**, replace with the instance.
- **B3** `(InductionScheme ℒₒᵣ (Hierarchy 𝚺 1)).Δ₁` → `𝗜𝚺₁.Δ₁` → **delete `axiom ISigma1_delta1Definable`**.

Put new lemmas in a new file (e.g. `Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.lean`)
imported by `Examples.lean`, to keep recompilation localized.

## ANTI-FRAUD + LOCK 🚫
- **Never** re-introduce an `axiom` or a `sorry` to "close" this. The whole point is to *remove*
  axioms; adding one (anywhere in the dependency chain) is failure.
- Do **not** weaken `Theory.Δ₁`'s definition or the axioms' types. Prove instances of the **same**
  `𝗣𝗔.Δ₁` / `𝗜𝚺₁.Δ₁` types.
- Disclosed sub-`sorry`s on intermediate lemmas during the grind are fine; the **win condition**
  is zero sorry + zero axiom on the final `𝗣𝗔.Δ₁` / `𝗜𝚺₁.Δ₁` instances.

## Self-stop (host-verified) 🛑
Stop when ALL hold:
1. `Examples.lean` contains **no `axiom`** (both replaced by proven instances).
2. `lake build Foundation` GREEN.
3. `#print axioms` on both instances = `[propext, Classical.choice, Quot.sound]`.

This is a clean, bounded objective — when it's met, the run is done. (Then: re-pin the downstream
Goodstein dep, and offer the branch upstream to FFL — it discharges their own TODO.)
