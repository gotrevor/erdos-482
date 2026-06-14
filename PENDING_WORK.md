# PENDING_WORK — Erdős #482 / Stoll

## ★ ACTIVE FRONTIER (2026-06-14): cubic self-referential impossibility (Tier-2)

**Where it stands.** The single-floor "Tier-1" the findings doc proposed is FALSE (refuted this lap:
`SelfRefWall.onefloor_div2_crux_cbrt2` — the cubic single floor IS solvable, `c=½`, like every `β<2`).
The genuine cubic obstruction is now *localized* by `General/CubicDefect.lean`:
- `cubic_threestep_defect` (✅ axiom-clean): the 3-step map `v₃=⌊α(⌊α(⌊α(u+c₀)⌋+c₁)⌋+c₂)⌋` satisfies
  `v₃ = 2u + (2c₀+α²c₁+αc₂) − (α²f₁+αf₂+f₃)`, `α³=2`, `fᵢ` the internal floor errors. So the extracted
  "digit" is `v₃−2u = C − (α²f₁+αf₂+f₃)`, `C := 2c₀+α²c₁+αc₂` a fixed real.
- `cubic_combined_defect_range_wide` (✅ axiom-clean): as `(f₁,f₂,f₃)∈[0,1)³`, the combined defect
  `α²f₁+αf₂+f₃` ranges over width `α²+α+1 > 1`, so it fits **no** width-1 window `[C,C+1]`. Two internal
  floors ⇒ spread > 1 (vs the single floor's spread = exactly 1, which is why `√2` barely closes).

**What remains for an UNCONDITIONAL impossibility — and an important caveat.** The missing link is:
*the geometric orbit `u_n ≈ W·α^n` actually realises a pair of `(f₁,f₂,f₃)` configs whose combined
defects differ by > 1* (then no fixed `C` keeps both digits in `{0,1}` — done, via the two lemmas above).
This is an equidistribution statement about `{α^n ξ}` for `α=2^{1/3}`.  **CAVEAT (corrects the findings
doc, which called this "guaranteed because α is non-Pisot"):** equidistribution of `{ξ·θ^n}` for a
*fixed* base `θ>1` and a *fixed* `ξ` is a notoriously OPEN problem (cf. the unknown distribution of
`{(3/2)^n}`). It holds for *almost all* `ξ` (Weyl/Koksma), but NOT known for the specific `ξ` our orbit
forces. So the unconditional cubic impossibility is **genuinely open in current mathematics**, not merely
unformalized — the doc over-claimed. *(Filed for cross-check: `ON-LINE-REQUEST.md`.)*

**Three attack paths (do real progress on one per lap):**
1. **Conditional impossibility (TRACTABLE — do next).** Formalize: *if* ∃ two orbit indices `n,n'` whose
   combined defects differ by `>1`, *then* the 3-step map fails to read base-2 digits. This is a clean
   combination of `cubic_threestep_defect` + a "two-points-don't-fit-a-window" lemma (analogous to
   `cubic_combined_defect_range_wide` but for two specific reachable points). Fully provable now; it
   packages exactly "the cubic fails modulo equidistribution," the honest ceiling.
2. **Almost-all-`W` version.** Use the a.e.-equidistribution of `{Wα^n}` (mathlib `AddCircle` ergodicity
   is for `n·θ`, NOT `θ^n` — would need the measure-theoretic Weyl/Koksma `{Wθ^n}` result, likely not in
   mathlib; check `Mathlib/Dynamics/`). Gives "for a.e. `W`, no fixed schedule reads `W`'s base-2 digits
   via the cubic map" — a true unconditional theorem about the *family*, sidestepping the open specific-`ξ`
   case. Higher infrastructure cost.
3. **Finite/uniform escape (NOW THE MOST PROMISING UNCONDITIONAL ROUTE — was mis-rated "probably false").**
   Probe whether, for *every* schedule `(c₀,c₁,c₂)`, the block-digit `v₃−2u` escapes `{0,1}` within a
   uniformly bounded number of blocks `N`. If `sup N < ∞`, a finite decidable check gives an
   **unconditional** cubic impossibility — no equidistribution needed, sidestepping the open `{α^n ξ}`
   problem entirely. **2026-06-14 evidence (`tools/sandbox/cubic_uniform_escape_probe.py`, float64):**
   random schedules fail in ≤52 blocks (mean 0.9); the literature triple `(1/6,1/3,4/3)` fails at ~51–64;
   a 31³ grid (span ±0.06) around it, varied starts, found **nothing past ~51** in float.
   **⚠️ But float64 caps at ~52 BECAUSE `u` doubles each block and hits the `2^53` integer wall —
   the "cap" is a PRECISION ARTIFACT, not a bound.** Exact `Decimal`(400-digit)+`Fraction` check
   (`first_fail_exact`): the doc triple genuinely fails at block **63** (matches doc "j=64"), and
   float's 52 was spurious. So float searches **cannot** resolve `sup N`. **Next concrete step:** run an
   **exact-arithmetic** search (rational offsets, `Decimal` orbit) — local-search/continuation maximising
   `first_fail_exact` — to see if any schedule survives ≫63. If `sup N` is finite, that finite bound +
   a decidable check gives the unconditional proof (the win). If survival climbs unboundedly under
   exact fine-tuning, the cubic needs the (open) `{α^n ξ}` equidistribution and only the CONDITIONAL
   theorem (`cubic_threestep_digit_pair_fails`, done) is provable. **This single exact search decides
   whether the cubic is unconditionally closeable** — highest-leverage next numerical experiment.
   **2026-06-14 exact-search result (partial):** an exact local search (rational offsets, 400-digit
   `Decimal` orbit) found a schedule surviving **≥91 blocks** — so the doc triple's 63 is NOT the sup and
   the earlier "sup ~64" guess is WRONG. The search then plateaued at 91, but that is almost certainly a
   local-search stall (discrete/non-convex landscape), not a true bound. **Verdict: leans toward
   `sup N = ∞` (path #3 likely dead → equidistribution genuinely required), but UNRESOLVED.** A proper
   test needs continuation / constraint-propagation (track the offset-polytope satisfying the first `k`
   digit constraints; check if it stays nonempty as `k→∞`), not random hill-climbing.

**⚠️ This file below is now largely historical — see [`STATUS.md`](STATUS.md) for the authoritative state.**
The project is **COMPLETE and axiom-clean** (zero `sorry`, zero custom axioms): the headline
(Graham–Pollak / √2), **Theorem 3.2 for all 7 non-special pairs (full ε-intervals)** + **Corollary 3.3**,
**and Stoll [St05] in full generality** (any `w>0`, any base `g≥2`: Thms 1.1, 1.2 I/II, 1.3, Cors
1.1/1.2, Prop 2) are all done. The §0 / §1b tracks below were written **while St05 was in progress
(2026-06-06)** and have **since been completed (2026-06-07)** — they're kept for the record. What
genuinely remains is **not actionable as theorems** (the pair-5 full interval and an all-8-pairs master
theorem are *not* theorems — §1, §2) plus optional cosmetic polish.

## 0′. 🆕 St06 FUN-EXTENSION (branch `st06`) — Theorem 3.1, remaining subcones (2026-06-13)

**St06 Theorem 3.1 is COMPLETE & axiom-clean** (`St06Thm31.lean`) — Tier 1 (Example 1.1) + all 12
sub-subcones `𝒟₁..₆ × {+,−}` via the cone-agnostic master `st06_thm31_closed_core`, the twelve
`d{1..6}{m,p}_core` interval lemmas, and the twelve `st06_thm31_d{1..6}{m,p}_digits`.  Corrected
ε-intervals `1+γᵢ^s ≤ ε < δᵢ^s` (erratum), verified ~250k pts.

**TIER 3 UPDATE (2026-06-13): Thm 3.3 (full), Thm 3.4 (ε=½), Cor 3.5 (FULL CAPSTONE) DONE.**
- ✅ **Thm 3.3** — `St06Thm33.lean`, both conclusions + full ε-interval + GP cross-check. Axiom-clean.
- ✅ **Thm 3.4 — RESOLVED (2026-06-13), like pair 5.** `St06Thm34.lean`: **ε=½** case (both conclusions,
  `st06_thm34_digits`/`_even_digits`) PLUS the full-interval **Diophantine obstruction**:
  `st06_thm34_bstep_value` (exact general-ε b-step value), `st06_thm34_bstep_band` (lands iff
  `frac∈(−d,1−d]`, cf. `pair5_estep_band`), `st06_thm34_band_fails_below_half`/`_above_half` (for ε<½ a
  d=1 boundary step breaks the upper band; for ε>½ a d=0 step breaks the lower — so no ε≠½ is
  t-universal). Stoll's printed interval is NOT a t-universal theorem; ε=½ is the proven ceiling. All
  axiom-clean. (PDF curiosity in `ON-LINE-REQUEST.md` is now non-blocking.)
- ✅ **Cor 3.5 — COMPLETE (2026-06-13), no PDF needed.** `St06Cor35.lean`: the GP recurrence
  `su √2 √2 ½ ½ n` from any `n>0` reads off the binary digits of `r·√2`, `r` fixed by which Beatty seq
  contains `n`. Engine = `gp_pair` generalized by a free factor `r` (`cor35_pair`/`_case2`,
  `cor35_floorA/B`, `cor35_base`); capstone `st06_cor35` (via `beatty_unique_sqrt2`); literal
  `st06_cor35_realDigits` (= `Real.digits (r√2) 2 j`) + `st06_cor35_isBit`. The off-by-M PDF concern
  was illusory — the tracked number is `r·α` (Beatty real); digits are those of `r√2`; Stoll's printed
  `w`-table is just a mantissa renormalization of the same digit string. All axiom-clean.

**Original Tier 3 transcription (kept for reference):**
- **Thm 3.3** (binary `g=2`): `u₁=m`, `a=2k+1+(t+2l)/(t+2m)`, `b=2/a`, `½−(2l+1)/(2(2m+1)) ≤ ε <
  ½+(2l+1)/(2(2m+1))` (interval **independent of k**); conclusion `u_{2n+1}−2u_{2n−1}=dₙ` AND
  `u_{2n+2}−2u_{2n}=d_{n+1}+k(2dₙ−1)`.  `√2,(1,0,0),ε=½` → Graham–Pollak.  **NUMERICALLY VERIFIED**
  (`tools/sandbox/st06_thm33_verify.py`, both conclusions, many params, both ε-endpoints) — KEY: `dₙ`
  is indexed with **`d₁` = the integer digit** (`dₙ = ⌊t·2^{n−1}⌋ − 2⌊t·2^{n−2}⌋`), same convention as
  `Cor13e.lean`.  (This repo's base-2 `Erdos482.Stoll` already has the √2 special case.)  Formalization
  plan: the closed forms are `u_{2n+1} = m·2ⁿ + ⌊t·2^{n−1}⌋` (the `digit_of_evenClosed_coeff` machinery
  in `St06Example.lean` already reads off conclusion (1)); conclusion (2) needs the even-index closed
  form `u_{2n} = …` (carry term with `k`).  Engine = a binary analogue of `st06_thm31_closed_core`.
- **Thm 3.4** (the other binary family): `a=2k+1+2l/(t+2m)`, k-dependent ε-bounds.
- **Cor 3.5** (Beatty unification): needs mathlib `Beatty`/`Nat.beattySeq` (confirm availability at
  v4.29.1).  Numerically verify every formula first (extend `tools/sandbox/st06_*.py`).

## 0. 🆕 NEXT TRACK — formalize Stoll [St05]: the REAL #482 resolution (any `w>0`, any base `g`)

**This is the highest-value open work** (added 2026-06-06). Erdős–Graham's "similar results for √m and
other algebraic numbers" is resolved by Stoll [St05] for *every* positive real `w` in *every* integer
base `g≥2` — and it's **elementary** (#403-tier), reusing this repo's `Crux`/`Induction`/`Digits`
machinery with the coefficients parametrized. Everything below (§1 pair-5, §2 master) is `0902.4168`
polish on the *α√2* sub-case; §0 is the actual generalization the problem is famous for.
- **Plan + milestones:** [`notes/ST05-GENERAL-PLAN.md`](notes/ST05-GENERAL-PLAN.md)
- **Verbatim targets + ⚠️ verify-don't-trust + ground-truth PDF:** [`papers/SOURCES.md`](papers/SOURCES.md)
  (`papers/St05-stoll-JIS2005.pdf`, gitignored).
- First milestone: Thm 1.2 **Case II** (binary, ε=½) as proof-of-concept the machinery parametrizes.
- **Note:** St05 does NOT inherit pair-5's Diophantine wall — its proofs close uniformly (see the plan).

## 1. Pair 5 (special `t₅ = √2`, β=0) — ✅ RESOLVED 2026-06-06 (the full interval is NOT a theorem)

**Outcome:** the online findings (`archive/findings/ON-LINE-FINDINGS-2026-06-06-pair5.md`) settled this.
Stoll's full-interval pair-5 claim `[0.49599…, 0.50124…)` is **essentially false** (the digit identity
fails at the stated lower endpoint at n=280); only **ε=½** works for all n — which is exactly the
headline Graham–Pollak. The printed pair-5 closed form also has a **typo** (`v_{2k}=⌊tᵢ2^{k−2}⌋+2^{k−2}`
gives v₂=½; correct is `⌊√2·2^{k−1}⌋+2^{k−1}`). So the honest content was formalized instead of chasing
a false interval. **All committed & axiom-clean (trust base only):**
- `stoll_pair5_closed_form` — Stoll's §4 explicit formula, typo-corrected (via `gp_pair`+`vv_half_eq_u`).
- `pair5_estep_band` — exact band characterization: the ε-step lands iff `B_j(ε):={√2·2^j}−√2·{√2·2^{j−1}}+√2ε ∈ [0,1)`.
- `stoll_pair5_conditional` — honest conditional full-interval theorem (base step + band ∀j ⟹ digits).
- `pair5_band_at_half` (B_j(½)=crux(√2·2^j), always holds) + `stoll_pair5_half_via_band` (GP via band route).
- `pair5_band_branch` (two-branch identity) + `pair5_band_fails_below_half`/`above_half` (precise obstruction, both sides).
- Diophantine infra: `fract_two_mul`, `fract_two_mul_branch`, `fract_sqrt2_pow_ne_half`, `sqrt2_pow_far_from_halfint`, `sqrt2_badly_approximable`.

The **admissible ε-set is exactly the band condition** (a Diophantine condition, possibly `{½}` if √2 is
normal — open), not an elementary interval. This is the complete honest story; no open obligation remains
on pair 5. (Historical analysis preserved below for the record.)

<details><summary>Historical (pre-resolution) analysis — kept for the record</summary>

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

**🛑 CORRECTION (later same lap — the `vv = u` reformulation is a DEAD END; read this before retrying):**
`vv ε = u` holds on `[ξ₁,ξ₂)` only for SMALL n. Verified far out: for the interior midpoint,
`vv ε` **diverges from `u` at n=905**, and the digit-difference `d_n` **first differs from √2's digit
at n=452**. So interior ε in the claimed interval `[309/2√2−218, 1296121037/2√2−916495974)` do NOT
reproduce √2's digits at large n. Either (a) this interval is WRONG/misread (the transcribed pair-5
eqs were already flagged suspect — predicted `vv3=2`, true `4`), or (b) the valid ε-set is subtler
than a full interval (possibly Cantor-like), or (c) the digit index has a phase I haven't pinned.
**`Heven` (∀ j) is therefore satisfiable essentially only at ε=½** — so `vv_eq_u_of_evenstep` /
`stoll_pair5_of_evenstep` (both committed, CORRECT axiom-clean conditionals) re-prove only the ε=½
case, NOT the interval. **Do not chase `vv = u` further.** Pair 5 needs the actual paper argument
(see `ON-LINE-REQUEST.md`) before more Lean work — formalizing against a wrong interval is wasted.
`sqrt2_badly_approximable` (committed, axiom-clean) is the likely Diophantine lever but only once the
correct statement is known.

**Superseded earlier guess (kept for the record):** "for ε ∈ [ξ₁,ξ₂), `vv ε n = u n` for all n; pair
5 ⟺ that + `graham_pollak`." FALSE for all n (see correction above).

**⚠️ This is genuinely Diophantine (NOT finite).** The per-step margin `min({√2(u_{2j}+½)}, 1−…)`
**shrinks as n grows**: ≥0.0037 for n<400, but **1.4e-6 at step 1811** (verified, prec=2200 ≫ needed
~905 digits). So `{√2·2^j}` gets arbitrarily close to the danger boundary; agreement holds for all n
only because √2 is a quadratic irrational (badly approximable, c.f. `[1;2,2,2,…]`) — a quantitative
Diophantine lower bound on `‖√2·2^j‖` is what keeps the margin positive forever. A finite base case
will NOT suffice; this needs a real Diophantine input (likely the hardest single piece of the project,
plausibly 🟠 generational). The headline already covers the key instance ε=½.

**Attack paths (all require new ideas, likely multi-lap):**
0. **(Primary) `vv ε = u` via Diophantine bound.** Prove `∀ ε∈[ξ₁,ξ₂), ∀ n, vv ε n = u n` by strong
   induction; the even-step reduces to a quantitative lower bound on `‖√2·2^j‖` (distance to nearest
   integer) for the quadratic irrational √2. Check mathlib for badly-approximable / quadratic-irrational
   Diophantine lemmas (e.g. `Real.sqrt`-irrationality + a `Liouville`-style bound for degree-2).
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

</details>

## 1b. St05 Theorem 1.3 (g-ary general) — ✅ DONE (2026-06-07)
Completed; see STATUS.md and `src/Erdos482/General/`. Verified numerically (`tools/sandbox/st05_thm13_verify.py`: w∈{√2,√3,π},
g∈{2,3,10}, ε-endpoints, many n — all OK). Done & axiom-clean:
- `General/Digits.lean` — `digitStep g x = ⌊gx⌋−g⌊x⌋`, range bound `0≤digitStep<g`; `gdigit` (Prop 2) + `gdigit_mem`.
- `General/Thm13.lean` — `thm13_digit_of_oddClosed`: given the odd closed form `u(2k+1)=g^k+⌊t·g^k/g⌋`,
  the difference `u(2n+1)−g·u(2n−1) = digitStep g (t·g^{n−1}/g) ∈ [0,g)`. This is Thm 1.3's conclusion
  **modulo the closed-form induction**.
- **Completed (2026-06-07):** the closed-form induction `thm13_closed` was proved locally (after the
  Aristotle job `e0240fef` stalled), ported onto the repo `gu` def, and chained to
  `thm13_digit_of_oddClosed` for an unconditional Thm 1.3 — plus Mantissa (1≤t<g), Prop 2, Thm 1.2
  Cases I/II, Cor 1.1/1.2, and the top-level `erdos482_resolution`. All axiom-clean (see STATUS.md).

## 2. Master theorem (Theorem 3.2, full ε-range)
For the 7 non-special pairs this is done. Pair 5 only holds at ε=½ (§1: the full interval is not a
theorem), so a single "∀ ε in the admissible range" master theorem over all 8 pairs is **not provable as
stated** — it would assert pair 5's false full-interval claim. The honest master statement is the 7-pair
cover (`stoll_intervals_cover` + the `stoll_pair{i}`) plus pair-5-at-½ (`stoll_pair5_half`); both done.

## 3. ~~Open research direction (out of scope)~~ — SUPERSEDED 2026-06-06
Previously: "'Generalize to other algebraic numbers' needs new mathematics, not a formalization gap."
**This was wrong.** Stoll [St05] already resolves it elementarily for any real `w` / any base `g` — it's
now the active **§0 NEXT TRACK** above, not out of scope.

## Notes for whoever continues
- The general core `stoll_pair`/`stoll_digit` (carry `αᵢ·2^{m+1}`) does NOT fit pair 5 (carry `2^j`
  on `P5`, `2^{j+1}` on `Q5`) — pair 5 needs its own core (`stollA`/`stollB` with a=1 are *close* but
  the carry-doubling lands on the wrong step). Don't try to reuse `stoll_pair` for pair 5.
- `cor33_base_of_bounds` (interior ε) and `cor33_base_interval` (full interval) + `stoll_pair7_base`
  use `set_option maxHeartbeats 1000000`/`4000000` — keep when editing. Base cases are
  **script-generated** (Python loop), don't hand-edit the 62 steps.
- mathlib v4.29.1: `lt_or_ge` (not `lt_or_le`); `pow_le_pow_left₀`; `Real.pi_gt_d6`/`pi_lt_d6`;
  `Real.exp_one_gt_d9`/`lt_d9`.
