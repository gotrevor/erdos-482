# HANDOFF — pointer (branch `st06`)

**You are on branch `st06`, NOT `main`.** The #482 core (Graham–Pollak + Stoll arXiv:0902.4168
Thm 3.2 / Cor 3.3 + St05 general base-`g` resolution) is **COMPLETE and axiom-clean on `main`**. This
branch is the **St06 "for fun" extension** (Stoll, *Acta Arith.* 125 (2006), 89–100) — now also
**COMPLETE and axiom-clean** (Example 1.1, Thm 3.1 all 12 cones, Thm 3.3 full, Thm 3.4 ε=½ + the
full-interval Diophantine obstruction, Cor 3.5 the Beatty capstone). **No open mathematical items.**

This is a THIN POINTER. The durable state lives in:
- **[`STATUS.md`](STATUS.md)** — the living overview + axiom ledger (refreshed each review lap).
- **Newest baton** — [`HANDOFF-2026-06-13-2240.md`](HANDOFF-2026-06-13-2240.md) (what just happened + next).
- **[`PENDING_WORK.md`](PENDING_WORK.md)** — §0′ St06 status / attack notes (now all ✅).

## Standing rules
- **DO NOT push** — work stays on `st06`; Trevor reviews/merges/pushes. Commit every green build.
- **verify-don't-trust** — numerically check every formula (extend `tools/sandbox/st06_*.py`) before
  formalizing. Keep everything **axiom-clean** (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`; no `sorry`, no custom axiom, no `native_decide`). Pre-commit gate runs `lake build`.
- New St06 Lean lives under `src/Erdos482/General/`.

→ Start: read `STATUS.md`, then the newest `HANDOFF-*.md`. Remaining work is optional polish only.
