# STATUS — Erdős #482 (Graham–Pollak √2 binary digits)

_Refresh each review lap._

## Build
`lake build` — **GREEN**, no `sorry`, no custom `axiom`.

## Axiom ledger
Every theorem below: `#print axioms` = `[propext, Classical.choice, Quot.sound]` (zero custom axioms).
| Declaration | |
|---|---|
| `Erdos482.crux`, `gp_pair`, `graham_pollak`, `digit_bridge`, `graham_pollak_digits` | headline |
| `Erdos482.stoll_pair`, `stoll_digit` | Thm 3.2 general core |
| `Erdos482.stoll_pair1/2/3/4/7/8` | Thm 3.2, all 7 non-special pairs |
| `Erdos482.cor33`, **`cor33_unconditional`** | Cor 3.3 (759250125√2) |

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

## BONUS — Stoll Theorem 3.2 + Corollary 3.3 (`src/Erdos482/Stoll.lean`) — **DONE, axiom-clean**
Previous handoff called this "genuinely paper-blocked"; it is now fully formalized.
- `vv ε` — Stoll's ε-parametrized sequence (`ε` on odd Stoll steps, `½` on even). 0-indexed `vv ε n = v_{n+1}`.
- `stoll_pair` — **general induction core (Thm 3.2 eqs 5/6)**: for `α:ℤ`, `ε∈[1−√2/2, √2/2)`, and a base
  case at `k=l+2`, the two floor identities hold for all `k=l+2+m`. Rederived a cleaner invariant than
  the paper — stated purely in `α√2`, the core needs **neither** `β`, `γ`, nor `α+β=2^{l+1}` (those only
  relabel `α√2`'s digits as `t_i`'s). ½-step = `crux` (eq 7); ε-step = `eq8_general` (eq 8).
- `stoll_digit` — **digit extraction**: `v_{2k+1} − 2v_{2k−1} = binDigit (α√2) (m+1)` (k=l+2+m).
- `stoll_pair1/2/3/4/7/8` — **all 7 non-special pairs** (α,l = (1,0),(11,3),(45,5),(181,7),(46341,15),(3,1));
  pair 5 (√2) = the headline; each extracts the digits of `α√2` for ε in the pair's interval. Base cases
  via `vv_even_to`/`vv_odd_to` + per-step `nlinarith` against the exact √2-expressed ξ endpoints.
- `cor33` — Cor 3.3 conditional on the (true) base values `vv ε 61=2592242074`, `vv ε 62=3665983898`.
- **`cor33_unconditional`** — **Stoll's TITLE RESULT, no hypotheses**: digits of `759250125√2` from the
  `ε=1−π²/e³` recurrence. Key: `ε≈0.50862` is interior to pair 6's tight interval, so the 62-step base
  case (`cor33_base_of_bounds`, script-generated, `linarith` + 13-digit √2 + π/e bounds) has comfortable
  margins. `floor_mul_sqrt2` pins `⌊c√2⌋` via exact integer inequalities (`⌊759250125√2⌋=2³⁰`, etc.).

## Open / next
- **Faithful `t_i` framing** (cosmetic): `binDigit ((α√2−β)/2^l) (j+l) = binDigit (α√2) j` — would restate
  the pair results in the paper's `t_i` form. Aristotle job `31ac9af6` (tconn) in flight.
- A pair-6 "for all ε in [ξ₁,ξ₂)" theorem (vs the specific Cor-3.3 ε) would need the eq-9 endpoint
  analysis (tight steps); deferred — see PENDING_WORK.
- "Generalize to other algebraic numbers" — open research direction, out of scope.
