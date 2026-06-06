# PENDING_WORK — Erdős #482

Headline (Graham–Pollak / √2) COMPLETE and axiom-clean. **BONUS (Stoll Thm 3.2 + Cor 3.3) now also
COMPLETE and axiom-clean** — see STATUS.md. This was the "paper-blocked" item; it is done, including
the unconditional title result `cor33_unconditional` (digits of `759250125√2`).

## Remaining (all optional polish / open directions)

### 1. Faithful `t_i` framing (cosmetic) — Aristotle `31ac9af6` (tconn) in flight
Our pair theorems state the result as "digits of `α_i√2`"; the paper says "digits of `t_i`" with
`t_i = (α_i√2 − β_i)/2^{l_i}`. These are the same sequence shifted by `l_i`:
`binDigit ((α√2−β)/2^l) (j+l) = binDigit (α√2) j` (j ≥ 1) — numerically verified, submitted to
Aristotle. Once proved, restate `stoll_pair{i}` in `t_i` form for a verbatim match to Theorem 3.2.
Three attack paths if doing it locally:
1. Unfold `binDigit`; `t·2^{j+l} = α√2·2^j − β·2^j`; `Int.floor_sub_intCast` pulls out the integer
   `β·2^j`; the `−β·2^j` and `−2·β·2^{j-1}` cancel. (ℕ-exponent care: `j+l-1 = (j-1)+l` needs `j≥1`.)
2. Prove a single-floor lemma `⌊t·2^{m}⌋ = ⌊α√2·2^{m-l}⌋ − β·2^{m-l}` for `m≥l`, then `binDigit`
   is its difference.
3. Hand to Aristotle (done) and port.

### 2. Pair 6 "for all ε in [ξ₁,ξ₂)" theorem (deferred)
`cor33`/`cor33_unconditional` cover pair 6 for the *specific* `ε = 1−π²/e³` (interior to the
interval). A "for all `ε ∈ [ξ₁,ξ₂)`" version (like pairs 1–4,7,8) is harder: the base values shift at
the endpoints, so the tight base-case steps need the EXACT √2-expressed ξ endpoints (Stoll's eq 9),
not loose rational bounds. The pair-6 interval is razor-thin (`[0.50124,0.51035)`) with billion-scale
`α`. Mechanically the 62 steps are like `cor33_base_of_bounds` but each tight step closes by
`nlinarith` against the exact ξ endpoint. Attack: generalize the eq-9 base-case argument abstractly
(prove the base for any pair from `α+β=2^{l+1}` + the interval), which would also simplify pairs 1–8.

### 3. Open research direction (out of scope per HANDOFF)
"Generalize to other algebraic numbers" — needs new mathematics, not a formalization gap.

## Notes for whoever continues
- The general core `stoll_pair`/`stoll_digit` is the reusable heart; any new pair = one base case
  (`vv_even_to`/`vv_odd_to` per step) + `floor_mul_sqrt2` for the two base floors + `stoll_digit`.
- `cor33_base_of_bounds` and the pair-7 base use `set_option maxHeartbeats` (1M / 4M) — the long
  `nlinarith`/`linarith` chains exceed the 200k default. Keep that when editing.
- Base-case lemmas are **script-generated** (see the lap journal / git log); regenerate, don't
  hand-edit 62 steps.
