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

**⚠️ Why this is genuinely HARD (verified numerically this lap — do NOT try the pair-6 recipe):**
The ε-step bracket is `f_{j+1} − √2·f_j + √2·ε` with `f_j = {√2·2^j}` and `f_{j+1} = {2·f_j}` (the
doubling map = the binary-digit shift of √2). Case split on the digit `⌊2f_j⌋`:
- `f_j < ½`: bracket `= f_j(2−√2) + √2ε ∈ [√2ε, 1−√2/2+√2ε)` ⊆ [0,1) **iff `ε < ½`**.
- `f_j ≥ ½`: bracket `= f_j(2−√2) − 1 + √2ε ∈ [−√2/2+√2ε, 1−√2+√2ε)` ⊆ [0,1) **iff `ε ≥ ½`**.

So the ε-step is **NOT uniformly in [0,1)** for any single ε≠½: when `ε<½`, a step with `f_j` just
above ½ would break it, and vice-versa. It works only because the *specific* `f_j = {√2·2^j}` never
land in the forbidden sub-band — e.g. for `ε<½`, no `j` has `f_j ∈ [½, (1−√2ε)/(2−√2))`. This is an
**infinitary Diophantine property of √2's binary digits**, NOT a finite check. Numerics: at the
interior midpoint the min step-margin is `0.0037` and stays `≥0.0037` over 400 steps; only step 14 is
exactly tight at ξ₁ and step 58 at ξ₂. The 2-tight-steps look like pair 6, but the *induction itself*
(not just a base case) needs the digit control, so a pair-6-style "finite base + `eq8_general` tail"
**will not close** — `eq8_general` does not apply to pair 5's ε-step (different bracket form). The
general `stoll_pair` core also cannot represent pair 5 (digit-phase off by 1; no odd index ever holds
the base value 3). This is why Stoll treats pair 5 specially and why its interval is the specific
`[0.49599…, 0.50124…)`.

**Attack paths (all require new ideas, likely multi-lap):**
1. **Find/port Stoll's actual pair-5 argument.** The transcribed eqs (5)/(6) for pair 5 in
   `archive/findings/…` do NOT match the data (they predict `vv3=2`; actual `vv3=4`) — the
   transcription is suspect for pair 5. APPEND an `ON-LINE-REQUEST.md` item for Stoll's §4 pair-5
   (`i=5`, β=0) proof verbatim, including how he bounds the ε-step over the interval.
2. **Prove the Diophantine band-avoidance lemma.** Show `∀ j, {√2·2^j} ∉ [½, (1−√2·ξ₁)/(2−√2))` and
   the symmetric upper band — equivalently a statement about runs in √2's binary expansion. May need
   a continued-fraction / `Liouville`-type input about √2. Hard but self-contained.
3. **ε-stability transfer.** Prove `vv ε (2k+1) − 2 vv ε (2k−1)` is constant in `ε` on `[ξ₁,ξ₂)`, then
   read off the value from the headline (`ε=½`). Stability proof is the same band-avoidance analysis.

**Reality check:** pair 5 may be the hardest single piece of the whole formalization — it is the only
part that is not "elementary floors + finite computation." Treat as a long-term thread; the headline
already covers its most important instance (ε=½).

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
