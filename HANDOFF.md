# HANDOFF — pointer (branch `st06`)

**You are on branch `st06`, NOT `main`.** The #482 core (Graham–Pollak + Stoll arXiv:0902.4168
Thm 3.2 / Cor 3.3 + St05 general base-`g` resolution) is **COMPLETE and axiom-clean on `main`**. This
branch is the **St06 "for fun" extension** (Stoll, *Acta Arith.* 125 (2006), 89–100) — now
**COMPLETE, axiom-clean, AND faithfulness-corrected**: Example 1.1, Thm 3.1 all 12 cones, Thm 3.3 full,
**Thm 3.4 genuine full symmetric interval** (the prior "Diophantine obstruction / only ε=½" was a
SWAPPED recurrence — corrected 2026-06-13, see newest baton), Cor 3.5 the Beatty capstone. Plus a NEW
result `SelfRefWall.lean`: the self-referential digit recurrence `⌊√g(u+c)⌋` works **iff g=2, c=½**.
**Open frontier**: cubic/higher-degree self-reference (research; `ON-LINE-REQUEST.md`).

**Live frontier (2026-06-14): the UNIFORM general degree-`d` (`α=2^{1/d}`) self-referential
impossibility.** Cubic AND quartic are COMPLETE & axiom-clean. The general-`d` **algebraic +
abstract-geometric obstruction skeleton is now COMPLETE & axiom-clean** (`RpowLinIndep.lean`
`rpow_lin_indep_int` via Eisenstein; `RpowWindow.lean` `rrt_window_gt_two`/`window_not_cover`;
`GeneralDefect.lean` `dStep_defect_identity` → `dStep_partial_mem_window`). Build 🟢 8293. Remaining =
the analytic `Tᵈ` assembly on the already-degree-agnostic engine (orbit-coordinate form +
equidistribution + geometry crux + headline).

This is a THIN POINTER. The durable state lives in:
- **[`STATUS.md`](STATUS.md)** — the living overview + axiom ledger (refreshed each review lap).
- **Newest baton** — [`HANDOFF-2026-06-14-1145.md`](HANDOFF-2026-06-14-1145.md) (general-`d` algebraic
  skeleton: the 4 bricks landed + the 4-step analytic-assembly next actions + gotchas).
- **[`PENDING_WORK.md`](PENDING_WORK.md)** — ★★★★★ authoritative general-`d` frontier + roadmap.

## Standing rules
- **DO NOT push** — work stays on `st06`; Trevor reviews/merges/pushes. Commit every green build.
- **verify-don't-trust** — numerically check every formula (extend `tools/sandbox/st06_*.py`) before
  formalizing. Keep everything **axiom-clean** (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`; no `sorry`, no custom axiom, no `native_decide`). Pre-commit gate runs `lake build`.
- New St06 Lean lives under `src/Erdos482/General/`.

→ Start: read `STATUS.md`, then the newest `HANDOFF-*.md`. **Lesson this lap: `#print axioms` clean ≠
statement-faithful — verify any "obstruction/not-universal" claim against the paper's recurrence.**
