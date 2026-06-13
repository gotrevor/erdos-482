# HANDOFF — St06 fun extension (branch `st06`)

**You are on branch `st06`, NOT `main`.** The #482 core (Graham–Pollak + Stoll arXiv:0902.4168
Thm 3.2 / Cor 3.3 + St05 general base-`g` resolution) is **already COMPLETE and axiom-clean on `main`** —
see `STATUS.md`. This branch is an **optional "for fun" extension**: formalizing **Stoll [St06]**,
*On a problem of Erdős and Graham concerning digits* (*Acta Arith.* 125 (2006), 89–100).

## Your task
Read **`notes/ST06-PLAN.md`** first — it has the full plan and the **transcribed statements** (the box
has no internet and the St06 PDF is gitignored, so that doc is your only source for the paper). Work the
tiers in order:
1. **Example 1.1** — the ternary digits of `e` via a recurrence with `π` and `e`. ✅ already numerically
   verified (`tools/sandbox/st06_example11_verify.py`, matches to n=40). Self-contained showcase — mirror
   `General/Cor13e.lean` / `cor33_unconditional`. Best fun-to-effort; do it first.
2. **Theorem 3.1** — the 3-parameter `(m,l,k)` family. Start with **one subcone (`𝒟₂⁻`)**, which contains
   Example 1.1, before the full 6-way split. Engine = St06 Prop 4.1 ≈ our `thm13_closed`.
3. **Thms 3.3 / 3.4** (binary families) + **Cor 3.5** (Beatty unification of Borwein–Bailey `m=1..10`).

## Rules
- **DO NOT push.** Work stays on `st06` locally; Trevor reviews / merges / pushes when it's done.
- **verify-don't-trust.** Numerically check every St06 formula before formalizing (extend the sandbox
  scripts). St06 is unverified except Example 1.1. Pair 5 had a false interval AND a typo — see
  `STOLL-PAIR5-ERRATUM.md`. If a claim fails numerically, scope it down + write an erratum note; do not
  formalize a false statement.
- **Reuse the existing machinery**: `Crux`, `Induction`, `Digits`, and especially `General/`
  (Prop 2 = `digitStep`/`gdigit`; `thm13_closed` = the closed-form induction engine ≈ St06 Prop 4.1).
- **Commit when green** (the `.githooks/pre-commit` gate runs `lake build`). Keep everything
  **axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`, no custom
  axiom, no `native_decide`). Refresh `STATUS.md` as targets land.
- New St06 Lean goes under `src/Erdos482/General/` (e.g. `St06Example.lean`, `St06Thm31.lean`).

→ Start: read `notes/ST06-PLAN.md`, then Tier 1 (Example 1.1).
