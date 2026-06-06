# STATUS — Erdős #482 (Graham–Pollak √2 binary digits)

_Refresh each review lap._

## Build
`lake build` — **GREEN**, no `sorry`, no custom `axiom`.

## Axiom ledger
| Declaration | `#print axioms` |
|---|---|
| `Erdos482.crux` | `[propext, Classical.choice, Quot.sound]` |
| `Erdos482.gp_pair` | `[propext, Classical.choice, Quot.sound]` |
| `Erdos482.graham_pollak` | `[propext, Classical.choice, Quot.sound]` |
| `Erdos482.digit_bridge` | `[propext, Classical.choice, Quot.sound]` |
| `Erdos482.graham_pollak_digits` | `[propext, Classical.choice, Quot.sound]` |

**Zero custom axioms.** Target achieved for the headline (🟢 elementary, no machinery wall).

## What is proved
- `crux (x)` — universal inequality `0 ≤ {x} − √2{x/2} + √2/2 < 1` (= Stoll eq (7), already general).
- `eq8` / `eq8_general` — Stoll eq (8) interval check (ε=1/2; and the full ε-interval).
- `gp_pair (j)` — the two faithful GP floor identities, by joint induction:
  - `u(2j+1) = ⌊√2·2^j⌋ + 2^j`
  - `u(2j+2) = ⌊√2·2^j⌋ + 2^(j+1)`
  (corrected from the HANDOFF's off-by-one exponents; verified numerically — digits read
  `0,1,1,0,1,…` matching `√2 = 1.0110101…₂`).
- `graham_pollak (n)` — HEADLINE: `u(2n+1) − 2u(2n−1) = binDigit √2 n`.
- `digit_bridge (x)` — for `1 ≤ x < 2`, `Real.digits (Int.fract x) 2 i = ⌊x·2^(i+1)⌋ − 2⌊x·2^i⌋`.
- `graham_pollak_digits (n)`, `gp_digit_seq (i)` — canonical forms against mathlib's `Real.digits`.
- `gp_reconstructs_sqrt2` — `Real.ofDigits (digits (fract √2) 2) = fract √2` (closes the loop).
- `binDigit_mem_zero_one`, `floor_two_mul_sub` — `binDigit` is a genuine bit.
- `binDigit_sqrt2_first_six` — concrete certificate: digits `0,1,1,0,1,0`.
- `u_pos`, `u_strictMono` — the sequence is `≥ 1` and strictly increasing.
- `irrational_fract_sqrt2`, `digits_sqrt2_not_eventually_zero`, `gp_diff_one_infinitely` —
  the expansion is that of an irrational and does **not** terminate (digit `1` occurs ∞ often).
- `digits_two_irrational_not_eventually_zero` (general: any irrational `y≥0` has non-terminating
  base-2 digits) and `digits_two_not_eventually_one` (general: no `0.0111…` tail for any `y≥0`).

## Open / next
- **BONUS (Stoll Thm 3.2 + Cor 3.3):** the 8 GP-style (α,β) pairs and the `759250125√2` corollary.
  Needs the paper's exact parametrized recurrence + the pair table — see `ON-LINE-REQUEST.md`.
  Infrastructure ready: `crux` is the general eq (7); `eq8_general` is the general eq (8).
- "Generalize to other algebraic numbers" — **open research direction, out of scope** (per HANDOFF).
