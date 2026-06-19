/-
# The headline: PA does not prove Goodstein's theorem (Kirby–Paris)

**Designated audit surface.** This is the open target of the expedition. It stays `sorry` until
the full reduction (`γ ⟹ Con(PA)` inside PA, via the ordinal analysis `TI(ε₀) ⊢ Con(PA)` +
Gödel II) is built — a genuine multi-month research milestone, NOT an overnight result.

⚠️ Anti-vacuity: this `sorry` is only meaningful once `goodsteinSentence` (`Encoding.lean`) is
the faithful encoding AND the bridge `(ℕ ⊨ goodsteinSentence) ↔ Goodstein-terminates` is proved.
Do NOT discharge this headline by introducing an `axiom` for the ordinal-analysis girder — that
would smuggle the whole theorem. A disclosed `sorry` here is the honest checkpoint; a bare
`axiom` standing in for `TI(ε₀) ⊢ Con(PA)` is not. See `DIRECTION.md`.
-/
import GoodsteinPA.Encoding

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove that every Goodstein sequence
terminates. (Open target; the proof reduces `γ` to `Con(𝗣𝗔)` and applies Gödel II.) -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence := sorry

end GoodsteinPA
