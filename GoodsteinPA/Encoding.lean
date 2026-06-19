/-
# Encoding "Goodstein terminates" as a first-order arithmetic sentence

This is the **Goodstein-independence expedition** (Kirby–Paris 1982): Peano Arithmetic does
not prove that every Goodstein sequence terminates. We build on **Foundation**
(`FormalizedFormalLogic`), which supplies first-order logic, PA (`𝗣𝗔 = Peano : ArithmeticTheory`
over `ℒₒᵣ`), Σ₁ arithmetization, and Gödel II (`LO.FirstOrder.Arithmetic.consistent_unprovable :
[Consistent T] → T ⊬ ↑T.consistent`).

## What `goodsteinSentence` must be
`γ` := the first-order `ℒₒᵣ`-sentence expressing **"∀ m, the Goodstein sequence started at m
reaches 0"** — a Π₂ sentence over the Σ₁ graph of the Goodstein step relation, built with
Foundation's `arithmetization` / sequence-coding API (`ISigmaOne`, hereditarily-finite-set
sequence coding in `FirstOrder.Arithmetic.HFS.*`).

The `:= sorry` below is a **stub**, not a claim. Replacing it with the real encoding is the
near-term work (see `DIRECTION.md`). The headline `peano_not_proves_goodstein`
(`Statement.lean`) is a faithful target only once two things hold:
1. `goodsteinSentence` is the genuine encoding (this file), and
2. the **faithfulness bridge** `(ℕ ⊨ goodsteinSentence) ↔ (every Goodstein sequence terminates)`
   is proved against the real (mathlib-side) Goodstein theorem. That bridge is the anti-vacuity
   certificate: a `sorry`'d `𝗣𝗔 ⊬ γ` against an unfaithful `γ` is worthless.

## Foundation API entry points (read the source — it's at `Foundation/FirstOrder/...`)
- PA: `𝗣𝗔` (notation for `Peano`), `Foundation/FirstOrder/Arithmetic/Schemata.lean`.
- Gödel II + `Con`: `FirstOrder/Incompleteness/{Second,Consistency}.lean`
  (`T.consistent : Sentence ℒₒᵣ`, `consistent_unprovable`).
- Σ₁ arithmetization / sequence coding: `FirstOrder/Arithmetic/HFS/*`, `Omega1/*`, `ISigma*`.
- Semantics (for the bridge): `ℕ ⊨ ·` model satisfaction over `ℒₒᵣ`.
-/
import Foundation.FirstOrder.Incompleteness.Second

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **The Goodstein sentence `γ`** (STUB — to be built; see the file header + `DIRECTION.md`).
The `ℒₒᵣ`-sentence "every Goodstein sequence terminates", encoded via Foundation's Σ₁
sequence-coding. Until this is the real encoding, the headline theorem is not yet faithful. -/
def goodsteinSentence : Sentence ℒₒᵣ := sorry

end GoodsteinPA
