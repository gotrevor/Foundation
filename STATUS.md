# STATUS — Foundation (Trevor's fork)

> 🛑 **FINISH-AND-STOP — bounded run.** Objective = the mathlib **v4.29.1 → v4.31.0** forward-port.
> **DONE = a fully GREEN `lake build`** (there is no theorem to prove this run). On green: commit,
> then write `~/src/.treadmill/Foundation.stop` (`source=lap` / `mode=build-green`) and stop. No
> side quests. See `DIRECTION.md`.

## Headline (this run)
A green `lake build` of the `Foundation` lib under `leanprover/lean4:v4.31.0` + mathlib `v4.31.0`,
with the faithfulness invariant **sorry/admit count ≤ 27** (the pre-bump baseline) and
`Final.lean`'s three `#print axioms` free of `sorryAx`.

## Current
- Branch `mathlib-v4.31`, HEAD `8b9eca6` — **BUILD RED** (Vorspiel + Logic/Semantics renames in
  progress; bump of toolchain/lakefile/manifest already committed).
- Patterns doc: `~/src/mathlib-bump-cookbook/v4.29.1-to-v4.31.0.md` (read + extend each lap).

## Axiom ledger
Not applicable as a self-stop gate here (build target is `Foundation/`, not `src/`). Faithfulness is
gated by the green build + the sorry-count baseline, host-verified on stop.
