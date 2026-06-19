# HANDOFF — Goodstein-independence expedition (2026-06-19, START)

## 👉 READ `DIRECTION.md` FIRST. UNBOUNDED expedition. Your lane is the `GoodsteinPA/` lib ONLY.

This is the FFL **Foundation** repo (branch `goodstein-pa-expedition`), hosting Track 2 of the
Goodstein effort: the syntactic **`𝗣𝗔 ⊬ γ`** (Kirby–Paris). Foundation is read-only substrate —
do NOT modify `Foundation/`, the toolchain, or the deprecation warnings. No self-stop.

## State at start (this commit)
- **Build GREEN.** `lake build GoodsteinPA` → `Built GoodsteinPA (1182 jobs)`. Foundation
  (incl. Gödel II `consistent_unprovable`, full arithmetization) is compiled + cached.
- This Foundation clone was migrated to **Lean v4.29.1 + mathlib v4.29.1** (2-line change; builds
  100% green) so the lean-yolo box (which bakes v4.29.1) runs it with no rebuild.
- **Scaffold (your work surface):**
  - `GoodsteinPA/Encoding.lean` — `goodsteinSentence : Sentence ℒₒᵣ := sorry` (STUB to build).
  - `GoodsteinPA/Statement.lean` — `peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence := sorry`
    (the headline; stays `sorry` — see anti-vacuity in DIRECTION).
  - `GoodsteinPA.lean` — lib root.

## Next bricks (see DIRECTION.md "milestone ladder")
1. **Encode `γ`** (Phase 0.2): replace the `goodsteinSentence` stub using Foundation's Σ₁ /
   HFS sequence-coding (`Foundation/FirstOrder/Arithmetic/HFS/*`, `Omega1/*`). Read the source.
2. **Faithfulness bridge** (Phase 0.3, crown jewel): vendor a snapshot of Track 1's Goodstein def
   (`~/src/lean-formalizations/.../Logic/Goodstein/Defs.lean`, frozen) into `GoodsteinPA/Model/`,
   then prove `(ℕ ⊨ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`. This is what makes the
   headline meaningful — build it before anything downstream.
3. **Phase 1**: surface `Con(𝗣𝗔)` + Gödel II (`consistent_unprovable`) in usable form.

## Key facts / reuse
- PA = `𝗣𝗔` (`Peano : ArithmeticTheory`), `Foundation/FirstOrder/Arithmetic/Schemata.lean`.
- Gödel II = `LO.FirstOrder.Arithmetic.consistent_unprovable : [Consistent T] → T ⊬ ↑T.consistent`.
- You may READ `~/src/lean-formalizations` (Track 1 — Goodstein def + the ε₀ growth theory that
  feeds Phase 3) but never build/commit into it (it's a running treadmill).
- ⚠️ Do NOT axiomatize the ordinal-analysis girder (`TI(ε₀) ⊢ Con(PA)`) to "close" the headline —
  that smuggles the theorem. Disclosed `sorry` only. See DIRECTION "Anti-vacuity".
- Reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/`.
