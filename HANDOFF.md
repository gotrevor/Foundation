# HANDOFF — Foundation mathlib v4.31.0 forward-port (2026-06-20, START)

## 👉 READ `DIRECTION.md` FIRST. Bounded objective: drive `lake build` GREEN under mathlib v4.31.0.

## State at start
- **Branch `mathlib-v4.31`**, HEAD `8b9eca6` ("WIP: mathlib v4.31 forward-port (Vorspiel +
  Logic/Semantics renames) -- BUILD RED").
- **Mechanical bump DONE**: `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are all at
  `leanprover/lean4:v4.31.0` / mathlib `v4.31.0`. The v4.31.0 mathlib oleans are present in
  `.lake/packages` (CoW-cloned — do NOT re-`cache get`).
- **Build is RED**: only ~49 of Foundation's own oleans built before the first unfixed break.
  The flagged areas are `Vorspiel` + `Logic/Semantics` renames (per the WIP commit), plus whatever
  v4.31 surfaces downstream.
- **Sorry baseline: 27** (pre-existing, upstream). The port must NOT exceed this.

## Next steps
1. `lake build` → read the first error in dependency order.
2. Match it to a pattern in `~/src/mathlib-bump-cookbook/v4.29.1-to-v4.31.0.md` (the `convert`
   over-split family is the most common; `ring`/`simpa` now hard-error on no-progress; several
   renames hard-error because the `@[deprecated]` alias was missing). Iterate one file with
   `lake env lean Foundation/<File>.lean`.
3. Fix, rebuild, repeat the cascade. Commit each green increment. Append any new pattern to the
   cookbook.

## Completion (see DIRECTION "COMPLETION protocol")
When `lake build` is fully GREEN + committed: write `~/src/.treadmill/Foundation.stop` with
`source=lap` / `mode=build-green` / `reason=…`, commit a final HANDOFF, end the turn. The host
re-verifies green before halting the run.

## Faithfulness
Mechanical adaptation only — never `sorry`/`admit`/`axiom` away an error, never change the toolchain
or a theorem statement. Keep `Final.lean`'s three `#print axioms` free of `sorryAx`.
