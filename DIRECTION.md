# DIRECTION — read FIRST (operator directive, 2026-06-20, Trevor via Ren)

## 🎯 BOUNDED OBJECTIVE: finish the mathlib **v4.29.1 → v4.31.0** forward-port of THIS repo.

The mechanical bump is already done (toolchain + `lakefile.toml` + `lake-manifest.json` are at
`v4.31.0`, and the `v4.31.0` mathlib oleans are CoW-cached in `.lake/packages`). **The remaining
work is purely SOURCE-LEVEL:** drive `lake build` from RED to **fully GREEN** by adapting this
repo's `.lean` source to mathlib v4.31's renames and behavior changes. There is **no theorem to
prove** — for this run, *a green `lake build` IS the headline*. When it's green, you are DONE
(completion protocol below).

This OVERRIDES the autonomy charter's "prove the headline theorem" framing and any older
DIRECTION/HANDOFF you find in git history (the GoodsteinPA expedition was un-vendored to
`~/src/goodstein-independence`; do NOT resurrect it here).

## The documented patterns — USE THEM (this is "well-established", not improvised)
- **`~/src/mathlib-bump-cookbook/v4.29.1-to-v4.31.0.md`** — the canonical symptom → cause → fix
  map for exactly this version jump (the `convert` over-split, `ring`/`simpa` now-erroring,
  `diff→sdiff` / `zero_le` / `ENNReal.mul_le_mul_*` renames, etc.). **READ IT at the start of
  every lap.** When you discover a NEW pattern, **append it to that file** (symptom → cause → fix)
  so the next lap and the rest of the fleet inherit it.
- The reference corpus (charter cross-lap memory):
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` — `grep -rl v4.31` it for
  freshly-distilled notes (e.g. `convert!` / `simpa … using!` as the 1-char faithful fix for
  v4.31's stricter default transparency).
- **Upstream reference (read-only):** your `WebFetch`/`WebSearch` work server-side, so you may
  fetch `github.com/FormalizedFormalLogic/Foundation` to see how UPSTREAM adapted a specific file
  to a newer mathlib. Adapt, don't blind-copy; preserve our local commits.

## Workflow (the build → fix → build cascade is NORMAL)
1. `lake build` — it surfaces errors in dependency order; fix the FIRST one.
2. Iterate on a single file fast with `lake env lean Foundation/Path/To/File.lean` (compiles that
   one file against the prebuilt oleans). Use `trace_state` to read the goal v4.31 actually produced.
3. Apply the cookbook pattern, delete the trace, rebuild. Fixing one file lets the build reach the
   next break — a cascade of fixes is expected, not a sign something is wrong.
4. **Commit every green `lake build` you actually saw succeed.** NEVER push (the host pushes).

## ⚠️ FAITHFULNESS — this is a mechanical adaptation, NOT a re-proof. Non-negotiable:
- **NEVER use `sorry` / `admit` / `axiom` to silence a build error.** The pre-existing sorry
  baseline is **27** — do NOT exceed it. The host green-confirm REFUSES to stop the run if the
  sorry count rose, so a "green via new sorries" port will just relaunch you to do it properly.
- **Do NOT downgrade the toolchain** or change the mathlib pin. Do NOT change what any theorem
  *states* — only adapt proofs/imports to compile.
- If one file is genuinely stubborn after real effort, leave it red and move to OTHER red files,
  then come back. Don't fixate; don't fake.
- The three `#print axioms` in `Final.lean` are faithfulness anchors — keep them free of `sorryAx`.

## ✅ COMPLETION protocol (do this EXACTLY when the port is finished)
When `lake build` is **fully GREEN (zero errors)** and you've committed it:
1. **Write the stop sentinel** at `~/src/.treadmill/Foundation.stop` (same path is in
   `$LEAN_STOP_SENTINEL`) with EXACTLY these three lines:
   ```
   source=lap
   mode=build-green
   reason=mathlib v4.31.0 forward-port complete — lake build green
   ```
2. Update + commit `HANDOFF.md` noting completion.
3. End your turn.

The HOST loop then re-runs `lake build` to confirm green before it stops the run (and refuses if
the sorry count grew). If you ever write the sentinel while the build is still red, no harm — the
host just relaunches you to keep porting. Write the sentinel **only** after a committed green build.

## Not your job (no side quests)
Don't add features, "improve" Foundation, refactor, or chase the 27 pre-existing sorries — just
make the existing code compile under v4.31. There is no new work to invent here.
