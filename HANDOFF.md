# HANDOFF — Erdős #482 (Graham–Pollak √2 binary digits)

## Status: HEADLINE COMPLETE, AXIOM-CLEAN. Bonus (Stoll Thm 3.2) paper-blocked.

`lake build` is **GREEN**, **no `sorry`, no custom `axiom`**. Every theorem ends at
`[propext, Classical.choice, Quot.sound]`. See `STATUS.md` for the axiom ledger.

## What is proved (all in `src/Erdos482/`)

- **`graham_pollak (n) (hn : 1 ≤ n)`** (`Main.lean`) — THE HEADLINE:
  `u(2n+1) − 2·u(2n−1) = binDigit √2 n` for `u 0 = 1`, `u(n+1) = ⌊√2·(u n + 1/2)⌋`.
- **`graham_pollak_digits`** (`Main.lean`) — canonical restatement against mathlib's `Real.digits`:
  the quantity is the `(n−1)`-th base-2 digit of `Int.fract √2` (= `n`-th digit of √2 after the point).
- **`binDigit_sqrt2_first_three`** (`Main.lean`) — end-to-end certificate: digits `0,1,1` (matches `√2=1.0110101…₂`).
- **`crux (x)`** (`Crux.lean`) — universal `0 ≤ {x} − √2{x/2} + √2/2 < 1` (= general Stoll eq (7)).
- **`gp_pair (j)`** (`Induction.lean`) — the two GP floor identities by joint induction:
  `u(2j+1) = ⌊√2·2^j⌋ + 2^j`, `u(2j+2) = ⌊√2·2^j⌋ + 2^(j+1)`.
- **`eq8` / `eq8_general`** (`Induction.lean`) — Stoll eq (8) interval check (ε=1/2; and full ε-interval).
- **`digits_eq_floor_sub (y) (hy0)`** (`Digits.lean`) — general: for `y ≥ 0`, `Real.digits y 2 i = ⌊y·2^(i+1)⌋ − 2⌊y·2^i⌋`.
- **`digit_bridge`** (`Digits.lean`) — the `[1,2)` corollary used by `graham_pollak_digits`.
- **`floor_two_mul_sub`, `binDigit_mem_zero_one`** (`Digits.lean`) — `binDigit` is a genuine bit.

### ⚠️ Correction made this lap
The original HANDOFF's identities (5)/(6) had **off-by-one exponents**. The faithful, numerically
verified forms are `u(2j+1)=⌊√2·2^j⌋+2^j` and `u(2j+2)=⌊√2·2^j⌋+2^(j+1)` (digits read `0,1,1,0,1,…`).
The even→odd induction step is exactly `crux`; the odd→even step is `eq8`.

## Proof architecture (for whoever extends this)
Recurrence over ℤ (`urec`, nonneg arg ⇒ `Nat.floor = Int.floor`) → each induction step is one
`Int.floor (↑z + c) = z` with `c ∈ [0,1)` supplied by `crux`/`eq8` (via `Int.floor_intCast_add` +
`Int.floor_eq_zero_iff`). The fractional-offset algebra closes by `linear_combination (2^…) * (√2·√2=2)`.

## Remaining work

### BONUS — Stoll Theorem 3.2 (8 GP pairs) + Corollary 3.3 (`759250125√2`)
**Paper-blocked.** Needs the exact parametrized recurrence + the (α,β,l,γ) table + Cor 3.3's numeric
facts — see `ON-LINE-REQUEST.md` (filed 2026-06-06). The machinery is **ready**: `crux` is the general
eq (7), `eq8_general` is the general eq (8); only the faithful per-pair statement + replayed `gp_pair`
induction remain. Do NOT guess the parametrization (a mis-stated index silently breaks faithfulness —
same trap as the off-by-one above).

### Out of scope
"Generalize to other algebraic numbers" — open research direction, not a theorem (per original plan).

## Aristotle
- `fca57695` (bridge) — DONE, independently proved `digit_bridge`, verified axiom-clean (cross-check). Harvested.
- `96d83ca4` (digitsgen) — IN FLIGHT: general `digits_eq_floor_sub`. On return: download, verify in-kernel
  + `#print axioms`, compare to local proof. Then submit the next bounded lemma (keep one in flight).
- Problem dirs live in `tools/aristotle/`.

## Corpus / doctrine
KB reference: `~/personal/claude/knowledge/core/projects/lean-journey/reference/` (not auto-loaded;
`ls` + `grep` before re-fighting friction). 🟢 elementary target — ZERO custom axioms achieved.
Commit gate: `.githooks/pre-commit` runs `lake build`. Related: [[erdos-403]], [[lean-treadmill]].
