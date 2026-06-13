# HANDOFF — pointer (branch `st06`)

**You are on branch `st06`, NOT `main`.** The #482 core (Graham–Pollak + Stoll arXiv:0902.4168
Thm 3.2 / Cor 3.3 + St05 general base-`g` resolution) is **COMPLETE and axiom-clean on `main`**. This
branch is the **St06 "for fun" extension** (Stoll, *Acta Arith.* 125 (2006), 89–100) — now
**COMPLETE, axiom-clean, AND faithfulness-corrected**: Example 1.1, Thm 3.1 all 12 cones, Thm 3.3 full,
**Thm 3.4 genuine full symmetric interval** (the prior "Diophantine obstruction / only ε=½" was a
SWAPPED recurrence — corrected 2026-06-13, see newest baton), Cor 3.5 the Beatty capstone. Plus a NEW
result `SelfRefWall.lean`: the self-referential digit recurrence `⌊√g(u+c)⌋` works **iff g=2, c=½**.
**Open frontier**: cubic/higher-degree self-reference (research; `ON-LINE-REQUEST.md`).

This is a THIN POINTER. The durable state lives in:
- **[`STATUS.md`](STATUS.md)** — the living overview + axiom ledger (refreshed each review lap).
- **Newest baton** — [`HANDOFF-2026-06-13-correction.md`](HANDOFF-2026-06-13-correction.md) (Thm 3.4
  faithfulness fix + SelfRefWall + what's next).
- **[`PENDING_WORK.md`](PENDING_WORK.md)** — §0′ St06 status / attack notes.

## Standing rules
- **DO NOT push** — work stays on `st06`; Trevor reviews/merges/pushes. Commit every green build.
- **verify-don't-trust** — numerically check every formula (extend `tools/sandbox/st06_*.py`) before
  formalizing. Keep everything **axiom-clean** (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`; no `sorry`, no custom axiom, no `native_decide`). Pre-commit gate runs `lake build`.
- New St06 Lean lives under `src/Erdos482/General/`.

→ Start: read `STATUS.md`, then the newest `HANDOFF-*.md`. **Lesson this lap: `#print axioms` clean ≠
statement-faithful — verify any "obstruction/not-universal" claim against the paper's recurrence.**
