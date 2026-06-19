# DIRECTION — read FIRST (operator directive, 2026-06-19, Trevor via Ren)

## ♾️ UNBOUNDED EXPEDITION — Goodstein independence over PA (Kirby–Paris). Your work is the `GoodsteinPA` library ONLY.

This is the FFL **Foundation** repo, on branch `goodstein-pa-expedition`, used as a host for our
Track-2 expedition. **Foundation itself is read-only upstream substrate — DO NOT modify it.**

### Your lane (hard rule)
- Work ONLY in `GoodsteinPA/` + `GoodsteinPA.lean`. That is the entire writable surface.
- **DO NOT touch `Foundation/`, `Mathlib`, the lakefile's Foundation lib, or the toolchain.** Do
  not "fix" Foundation's 416 deprecation warnings — they are upstream's, harmless, out of scope.
  (This clone is pinned to Lean v4.29.1 + mathlib v4.29.1 deliberately; leave that alone.)
- `lake build GoodsteinPA` is your build; Foundation is already compiled and cached.

### What this expedition is
**Kirby–Paris (1982): `𝗣𝗔 ⊬ γ`**, where `γ` ("every Goodstein sequence terminates") is a
first-order `ℒₒᵣ`-sentence. The *positive* theorem (Goodstein terminates) and its *growth theory*
are Track 1, already done / in progress in `~/src/lean-formalizations` (you may READ it). This
track is the **syntactic, metamathematical** half, built on Foundation's logic apparatus.

This runs lap after lap until Trevor stops it. **No self-stop, `--allow-stop` is OFF.** The
headline will stay `sorry` for a long time — that is expected and correct (see ceiling below).

## ⚠️ Anti-vacuity — the danger on THIS track is a fake/vacuous "proof". Non-negotiable:
- **The headline `peano_not_proves_goodstein` stays `sorry`** until the real reduction is built.
- **NEVER discharge it (or its girder) with a bare `axiom`.** Introducing `axiom
  ti_eps0_proves_con_pa` (or any axiom that *is* the ordinal analysis / the consistency reduction)
  and citing it to "close" the headline is **smuggling the whole theorem** — explicitly forbidden.
  A disclosed `sorry` on an open crux is the honest checkpoint; an axiom standing in for the
  load-bearing metatheorem is not.
- **`γ` must be faithful, and the certificate is the bridge.** A `sorry`'d `𝗣𝗔 ⊬ γ` against an
  unfaithful `γ` is worthless. So the bridge `(ℕ ⊨ γ) ↔ (every Goodstein sequence terminates)` is
  the highest-value near-term deliverable — it ties the syntactic `γ` to the real (mathlib-side)
  Goodstein theorem. Build `γ` and this bridge before the headline means anything.
- Where you can, add executable/`native_decide` sanity anchors (e.g. the encoded step relation
  agreeing with concrete Goodstein steps) — off any headline axiom path.

## Milestone ladder (pick the next brick; the cruxes are flagged)
**Phase 0 — faithful statement (the bounded, achievable near-term work):**
- 0.2 **Encode `γ`** (replace the `goodsteinSentence` stub in `Encoding.lean`). Study Foundation's
  Σ₁ arithmetization / HFS sequence-coding (`Foundation/FirstOrder/Arithmetic/HFS/*`, `Omega1/*`,
  `ISigma*`) — read the source; the box has no web. Define the Goodstein step relation as a Δ₀/Σ₁
  formula, then `γ` := the Π₂ sentence "∀ m ∃ N, sequence from m is 0 at step N".
- 0.3 **Faithfulness bridge** (anti-vacuity certificate). To state/prove it you need the real
  Goodstein def: **vendor a snapshot** of `~/src/lean-formalizations/src/.../Logic/Goodstein/`
  (`Defs.lean` etc. — mathlib-only, frozen/done) into `GoodsteinPA/Model/` (copy + adjust imports;
  do NOT path-depend on the live `lean-formalizations` repo — it's a running treadmill). Then prove
  `(ℕ ⊨ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`. **This is the crown jewel of Phase 0.**
- 0.4 The headline `peano_not_proves_goodstein` is already stated (`Statement.lean`); keep it `sorry`.

**Phase 1 — Gödel II hook:** surface `Con(𝗣𝗔)` and `𝗣𝗔 ⊬ ↑𝗣𝗔.consistent` from Foundation
(`consistent_unprovable`, `FirstOrder/Incompleteness/{Second,Consistency}`) in usable form, and
state the meta-reduction target "`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`" so the headline collapses to one implication.

**Phase 2 — the ordinal-analysis girder (flagship core; months, human-architected):**
`TI(ε₀) ⊢ Con(𝗣𝗔)` (Gentzen) — infinitary `PA_∞`, ordinal assignment `< ε₀`, ε₀-bounded
cut-elimination. This is *originating* a major body of proof theory; it will NOT close in a night.
Each lap **advance** it (formalize one prerequisite, decompose the next sub-lemma) — never axiomatize it.

**Phase 3 — `Goodstein ⟹ TI(ε₀)`:** big reuse — Track 1's `Engine`/`Growth` already maps Goodstein
states to ordinals `< ε₀`; Phase 3 re-expresses that descent syntactically.

## Realistic ceiling (be honest, don't fake)
Tonight/this-week the achievable real progress is **Phase 0** (faithful `γ` + the bridge) and
beginning **Phase 1**. Phase 2 is a multi-month frontier. Measure success by: a faithful encoding,
a proved bridge, and prerequisite lemmas accumulated toward the girder — NOT by the headline
flipping. A lap that encodes part of `γ`, proves a bridge sub-lemma, or formalizes one girder
prerequisite is a successful lap.

## Rules (same as every autonomous run)
- Commit every green `lake build GoodsteinPA` you actually saw succeed. **NEVER push** (host pushes).
- Verify `#print axioms` on anything you close (must be the bare trust base; no `sorryAx`, no
  smuggled axiom). `native_decide` may appear only on standalone anchors.
- Verify names against THIS repo (Lean v4.29.1, mathlib v4.29.1, Foundation). Read Foundation's
  source for its API — you have no web.
- Reference corpus (cross-lap memory, not auto-loaded):
  `~/personal/claude/knowledge/core/projects/lean-journey/reference/` — `ls` + `grep -rl` it.
- Blocked needing the open web? Append to `ON-LINE-REQUEST.md` and continue on another brick.
- Keep `HANDOFF.md` current; at the budget, `/handoff` and end the lap.

## NOT a stop condition
No completion sentinel. Do not write `$LEAN_STOP_SENTINEL`. Do not stop because a milestone landed
or the next crux is hard. Keep building. Trevor ends the run.
