# Cubic self-referential recurrence — exploration (2026-06-13)

**Question.** Stoll's Graham–Pollak recurrence `u(n+1)=⌊√2(u(n)+½)⌋` reads off binary digits because
`√2·√2 = 2`: the *two*-step map is (up to a uniform `[0,1)` crux, `Erdos482.crux`) multiply-by-2. Does
the analogue work for a **cubic** irrational `α = 2^{1/3}` (`α³ = 2`), where a *three*-step map should
be multiply-by-2 — extending the whole edifice beyond quadratic irrationals?

**Finding: NO (the quadratic structure is special).** Numerically (`tools/sandbox/cubic_*.py`):
- A single offset `c` (recurrence `u(n+1)=⌊α(u(n)+c)⌋`) gives no clean bitstream at any phase.
- A **3-phase** offset triple `(c₀,c₁,c₂)` (offset depends on `n mod 3`) does produce a bitstream
  `u(3j+r)−2u(3(j−1)+r) ∈ {0,1}` for the first ~60 terms — e.g. `(1/6, 1/3, 4/3)` at phase 0. This
  looked promising.
- But it **breaks down**: extending the check, phase 0's first non-bit (a difference of `2`) appears at
  `j = 64`; phases 1,2 fail much earlier (`j=4`, `j=2`). The recovered limit `W = lim u(3j)/2^j ≈
  1.24986624` is **not** a clean `a+b·2^{1/3}+c·2^{2/3}` with small integer coefficients, and
  `u(3j) ≠ ⌊W·2^j⌋` (the closed form fails).

**Why.** The two-step √2 crux `0 ≤ {x} − √2{x/2} + √2/2 < 1` is *uniform* in `x` (a single quadratic
`nlinarith`). The three-step cubic analogue requires three intermediate floors to align simultaneously;
there is no offset triple making the combined error stay in `[0,1)` for all fractional parts — the
miss-margin shrinks and eventually a step overflows (the `j=64` failure). This is a genuine Diophantine
/ "needs new math" wall, NOT a formalization gap: the elegant self-referential digit extraction is a
quadratic-irrational phenomenon (Stoll's results, and St05's general track, already cover *reading any
real's digits* with a base-`g`-tuned recurrence — the special thing about √2 is that the recurrence's
own coefficient equals the number's algebraic generator).

**Status.** Closed as a negative exploration. If revisited, the open sub-questions are: (a) is there a
*non-constant-modulus* (non-3-periodic) offset schedule that works? (b) does a genuinely different
cubic construction (not `⌊α(·+c)⌋`) read off base-2 or base-`N` digits of cubic irrationals? Both look
like real research, not a lap-scale formalization.

**UPDATE 2026-06-13 — the wall is now a FORMALIZED THEOREM, and it is base-2-quadratic, not
cubic-vs-quadratic.** `src/Erdos482/General/SelfRefWall.lean` proves
`selfref_crux_solvable_iff`: the self-referential crux `0 ≤ {x} − √g·{x/g} + c·√g < 1` (the
`g`-analogue of `Erdos482.crux`) is solvable for *some* offset `c`, for all `x`, **iff `g = 2`**
(and then `c = ½`).  For every integer `g ≥ 3` it fails for every `c`
(`selfref_crux_fails_of_three_le`), by two explicit witnesses `x = g−1` and `x = 1/2` that pin `c`
into the empty interval `[(g−1)/g, 1/g]`.  So the obstruction is not *cubic* per se — it already kills
the **quadratic** self-referential extractor `⌊√g·(u+c)⌋` for base `g ≥ 3` (e.g. `√3` reading base 3).
The √2 / base-2 case is the unique survivor.  The cubic `2^{1/3}` 3-step map is a further, separate
failure of the same flavour (three floors can't align), still open as sub-questions (a)/(b) above, but
the headline "self-reference is a base-2 miracle" is now machine-checked.
