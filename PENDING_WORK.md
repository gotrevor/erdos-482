# PENDING_WORK — Erdős #482 / Stoll

Headline (Graham–Pollak / √2) and **Theorem 3.2 for the 7 non-special pairs (full ε-intervals)** +
**Corollary 3.3** are COMPLETE and axiom-clean — see STATUS.md. Verbatim `tᵢ`-form restatements and
the disjoint-and-cover completeness theorem are done. Remaining work below.

## 1. Pair 5 full-interval (the special `t₅ = √2`, β=0 case) — the real open thread

Pair 5 is the only pair without a vv-based interval theorem. It's proved at ε=½ by the headline
(`graham_pollak` via the `u` sequence), but Stoll's Theorem 3.2 asserts it for the whole interval
`ε ∈ [309/2·√2 − 218, 1296121037/2·√2 − 916495974) = [0.49599…, 0.50124…)`.

**Invariant (numerically verified this lap, midpoint + ε=½):**
- `P5(j): vv ε (2j+1) = ⌊√2·2^j⌋ + 2^j`   (odd index)
- `Q5(j): vv ε (2j+2) = ⌊√2·2^j⌋ + 2^{j+1}`   (even index)
- Digit: `vv ε (2k+1) − 2 vv ε (2k−1) = P5(k) − 2 P5(k−1) = ⌊√2·2^k⌋ − 2⌊√2·2^{k−1}⌋ = binDigit √2 k`.
  (Note the phase: index `k`, vs pairs 1–8 which give `binDigit (αᵢ√2) (m+1)` at `k = lᵢ+2+m`.)

**Step structure (derived; verify in Lean):**
- `P5(j) → Q5(j)` (from `vv(2j+1)`, index `2j+1` ODD ⇒ ½-step): bracket `(1−√2){√2·2^j} + √2·½` —
  this **is** `eq8_general` at `ε=½`. UNIFORM, easy.
- `Q5(j) → P5(j+1)` (from `vv(2j+2)`, index `2j+2` EVEN ⇒ ε-step): bracket
  `{x} − √2{x/2} + √2·ε` with `x = √2·2^{j+1}`. **NON-UNIFORM in x**: `crux` only gives
  `{x}−√2{x/2} ∈ [−√2/2, 1−√2/2)`, so `bracket ∈ [−√2/2+√2ε, 1−√2/2+√2ε)`, which ⊆ [0,1) *uniformly*
  only at ε=½. For ε≠½ in the interval, correctness depends on the SPECIFIC `{√2·2^{j+1}}` values
  avoiding the boundary — this is exactly what pins the pair-5 interval. **This is the hard core.**

**Attack paths:**
1. **Tight-step base + uniform tail.** Like pair 6: prove a finite base case (the first few `j` where
   `{√2·2^{j+1}}` is near the boundary, the tight steps) via exact endpoint bounds, then show the tail
   steps have comfortable margin. But the constraint recurs at every ε-step, so there may be NO
   uniform tail — check numerically whether `{√2·2^{j+1}}` stays bounded away from the bad zone for
   all large j (equidistribution suggests it gets arbitrarily close, so the endpoints may be a liminf).
2. **Reduce to the headline.** For ε=½ exactly, `vv ½ = u` and `graham_pollak` gives it. A "the digit
   is ε-stable on the interval" lemma would transfer the headline — but proving ε-stability is the
   same hard analysis.
3. **Endpoint-defining steps only.** Identify (numerically) which finitely many ε-steps are tight at
   the interval endpoints (like pair 6's steps 30/58); those define `ξ₁₅/ξ₂₅` and close by exact
   endpoint bounds; the rest by `eq8_general`-with-margin. FIRST verify in Python which steps bind.

**Do numerics first** (per project discipline): before any Lean, confirm in Python (a) the invariant
holds across the whole half-open interval, (b) which ε-steps are tight at each endpoint, (c) whether a
uniform-margin tail exists. Only then write the core.

## 2. Master theorem (blocked on pair 5)
Once pair 5 lands: `∀ ε, 1−√2/2 ≤ ε → ε < √2/2 → ∀ k ≥ 31, vv ε (2k+1) − 2 vv ε (2k−1) ∈ {0,1}`,
proved by `rcases stoll_intervals_cover`, applying the matching `stoll_pair{i}` with `m := k − (lᵢ+2)`
(re-index via omega; all pairs stable for `k ≥ 31` since max `lᵢ+2 = 31`), then `binDigit_mem_zero_one`.
The 7 non-pair-5 cases already work; only the pair-5 interval case needs item 1.

## 3. Open research direction (out of scope per HANDOFF)
"Generalize to other algebraic numbers" — needs new mathematics, not a formalization gap.

## Notes for whoever continues
- The general core `stoll_pair`/`stoll_digit` (carry `αᵢ·2^{m+1}`) does NOT fit pair 5 (carry `2^j`
  on `P5`, `2^{j+1}` on `Q5`) — pair 5 needs its own core (`stollA`/`stollB` with a=1 are *close* but
  the carry-doubling lands on the wrong step). Don't try to reuse `stoll_pair` for pair 5.
- `cor33_base_of_bounds` (interior ε) and `cor33_base_interval` (full interval) + `stoll_pair7_base`
  use `set_option maxHeartbeats 1000000`/`4000000` — keep when editing. Base cases are
  **script-generated** (Python loop), don't hand-edit the 62 steps.
- mathlib v4.29.1: `lt_or_ge` (not `lt_or_le`); `pow_le_pow_left₀`; `Real.pi_gt_d6`/`pi_lt_d6`;
  `Real.exp_one_gt_d9`/`lt_d9`.
