# STATUS — erdos-482 📊

**Stoll's binary-digits-of-759250125√2 (generalizes Graham–Pollak / Erdős #482), formalized in Lean 4.** · **Build**: 🟢 green (8273 jobs) · **Updated**: lap 2026-06-13 (`st06` branch, HEAD `1f844c2`) (**#482 COMPLETE & axiom-clean on `main`; St06 fun-extension on `st06`: Tiers 1+2 done, Tier 3 = Thm 3.3 full + Thm 3.4 (ε=½) + Cor 3.5 CAPSTONE now done — ALL St06 main theorems formalized**)

## 🎁 St06 fun-extension (branch `st06`) — Tier 3 COMPLETE (2026-06-13)
All axiom-clean (`[propext, Classical.choice, Quot.sound]`), build green (8273 jobs):
- **Thm 3.3** (binary family 1, `St06Thm33.lean`) — BOTH conclusions, full ε-interval `½±(2l+1)/(2(2m+1))`:
  `st06_thm33_{acrux,bcrux,closed,digits,even_digits,grahampollak}`. Even closed form
  `su(2j+1)=2k·A+(m+l)2ʲ+⌊t·2ʲ⌋+k`; the hard nonlinear b-crux proved locally (the `s` cancels → `y∈[0,1)`).
- **Thm 3.4** (binary family 2, `St06Thm34.lean`) — `a=2k+1+2l/(t+2m)`, even form `(2k+1)A+k+l·2ʲ`;
  `st06_thm34_{acrux,bcrux,closed,digits,even_digits}` (concl. 2 = `(2k+1)dₙ−k`).
  **⚠️ FULL INTERVAL CORRECTED 2026-06-13 (ON-LINE findings, `archive/findings/…thm34.md`).** The
  prior lap's "Diophantine obstruction / ε=½ is the ceiling" was an artifact of a **swapped recurrence**
  (`ε` on the b-step = Theorem **3.3**'s placement). Stoll's actual 3.4 puts `ε` on the **a-step**
  (`su a b ε (1/2) m`), which is `t`-uniform, so the **full symmetric interval is a GENUINE theorem**:
  `st06_thm34_astep_eps` (a-step floor crux for every `ε ∈ ½ ± (m−l+½)/D₁`, `D₁=(2m+1)(2k+1)+2l`,
  uniform over all `t∈[1,2)`, no Diophantine input), and `st06_thm34_{closed,digits,isBit}_eps` (full
  closed forms / conclusion-(1) digit theorem / bit, for every `ε` in the interval). The `ε`-on-b-step
  theorems (`st06_thm34_bstep_value/band`, `_band_fails_below/above_half`) are kept, **re-labeled
  `[SWAPPED-VARIANT, NOT Thm 3.4]`** — sound Lean about the 3.3-placement, but not about Theorem 3.4.
  Lesson: `#print axioms` clean ≠ statement-faithful.
- **Cor 3.5** (Beatty capstone, `St06Cor35.lean`) — **COMPLETE this lap, no PDF needed**. The GP
  recurrence `su √2 √2 ½ ½ n` started at any `n>0` reads off the binary digits of `r·√2` for the unique
  `r≥1` fixed by which Beatty sequence (`1+√2` / `1+1/√2`) contains `n`:
  - engine `cor35_pair`/`cor35_pair_case2` (gp_pair generalized by a free factor `r`; `cor35_floorA/B`
    + `cor35_base` from `crux`/`eq8_general`), digit forms `cor35_digits_case1/case2`;
  - `beatty_start_case1/case2` identify the starts with `beattySeq`; capstone **`st06_cor35`** via
    `beatty_unique_sqrt2`; literal **`st06_cor35_realDigits`** (= `Real.digits (r√2) 2 j`) + **`st06_cor35_isBit`**.
  - KEY INSIGHT: the tracked number is `w(m)=r·α` (Beatty real), digits are those of `r√2`; Stoll's
    printed `w`-table is just a mantissa renormalization of the same digit string (so the off-by-M PDF
    concern was illusory). Foundation lemmas (`holderConjugate_one_add_sqrt2`, `beatty_partition_sqrt2`,
    `beatty_unique_sqrt2`) unchanged.

## 🏆 St05 COMPLETE — Erdős #482 resolved in full generality (2026-06-06)
The whole of Stoll [St05] is now machine-checked and **axiom-clean** (`src/Erdos482/General/`):
**Thm 1.1** (Rabinowitz–Gilbert, `Thm11.lean`), **Thm 1.2 Case I** (ε-interval `[1/3,2/3)`, `Thm12CaseI.lean`)
+ **Case II** (ε=½, `Thm12.lean`), **Thm 1.3** (g-ary, any base — the headline, `Thm13Closed.lean`:
`thm13_closed`+`thm13_digits`), **Cor 1.1** (both √2 binary families, `Cor11.lean`), **Cor 1.2** (ternary
√2, `Cor12.lean`), **Prop 2** (`Digits.lean`). Top-level packaging: **`erdos482_resolution`**
(`Erdos482General.lean`) — for any `w>0`, any `g≥2`, an explicit recurrence reads off `w`'s base-`g`
digits. The joint-induction obligation the stalled Aristotle job `e0240fef` couldn't crack was proved
locally. Every declaration `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
**St06 resolved as a non-blocker** (2026-06-07): online-fetch came back (`archive/findings/…-st06.md`) —
its text is genuinely unobtainable (broken IMPAN SPA; not on arXiv/shadow libs) **and not on the
critical path** (St05 *is* the resolution; St06 only adds sharper restatements + showcase constants).
Nothing core remains open; what's left is optional showcase/polish.

## 🎁 St06 fun-extension (branch `st06`) — Tier 1 DONE (2026-06-13)
**Example 1.1 — the ternary digits of `e` via a negative-coefficient `π`/`e` recurrence** — is
formalized and **axiom-clean** (`src/Erdos482/General/St06Example.lean`):
- `su` — the St06 recurrence with general odd-offset `ε`, even-step shift `s`, start `m`
  (St05's `gu` = the `s=1/(g−1)`, `m=1` case).
- `st06_example11_ternary_e` / `_literal` — for `su (−3/(e+9)) (−(e+9)) π 1 3`, the Graham–Pollak
  difference `su(2n)−3·su(2n−2)` is exactly the `n`-th base-3 digit of `e` (`Real.digits e 3 (n−2)`).
  Proved via the joint closed-form induction `ex11_closed` (`su(2k)=3·3ᵏ+⌊e·3ᵏ/3⌋`,
  `su(2k+1)=−(3ᵏ+1)`) — the negative-`a`,`b` analogue of `thm13_closed`.
- `digit_of_evenClosed_coeff` — generalized digit extraction allowing ANY leading coefficient `c·gᵏ`
  in the even closed form (St06's `m·gᵏ` vs St05's `gᵏ`); reusable for Tier 2.

**Erratum found & recorded** (`notes/ST06-THM31-ERRATUM.md`): the `notes/ST06-PLAN.md` transcription of
St06 Thm 3.1's ε-interval for subcone 𝒟₂⁻ has a spurious "+1" on the upper endpoint — the correct
(numerically verified, ~1M points) interval is `1+γ₂⁻ ≤ ε < δ₂⁻` (not `< 1+δ₂⁻`).

### Tier 2 — St06 Theorem 3.1 COMPLETE (all 6 cones, both signs — 2026-06-13)
**The entire headline of St06 (Theorem 3.1, the 3-parameter `(m,l,k)` family) is formalized and
axiom-clean** (`src/Erdos482/General/St06Thm31.lean`), across **all 12 sub-subcones** `𝒟₁..₆ × {+,−}`:
- `st06_thm31_closed_core` — a **cone-agnostic master** joint-induction taking the even→odd inequality
  core as an abstract hypothesis; the odd→even step and closed-form induction are shared by every cone
  (and it needs only `t+mg ≠ 0`, so it serves both `Ω₁` `P>0` and `Ω₂` `P<0` unchanged).
- twelve `*_core` interval lemmas `d{1..6}{m,p}_core` (the even→odd two-sided bound, one per
  sub-subcone) + twelve `st06_thm31_d{1..6}{m,p}_digits` (GP difference = base-`g` digit of `w`):
  - `Ω₁` (`m≥1`, `P=t+mg>0`): `𝒟₁±, 𝒟₂±, 𝒟₃±` (l<0, 0<l≤g−1, l>g−1; k≷0).
  - `Ω₂` (`m≤−2`, `P<0`, the `÷(g−1)P` step flips via `div_lt_one_of_neg`+`neg_div_neg_eq`):
    `𝒟₄±, 𝒟₅±, 𝒟₆±`.
  All with `(g−1)∣(k−1)l`, every `#print axioms` = the trust base.
- `st06_example11_from_thm31` — Example 1.1 recovered as the `𝒟₂⁻` instance `(3,3,2,−1)`, `t=e`, `ε=π`.

**Comprehensive erratum** (`notes/ST06-THM31-ERRATUM.md`): the correct Thm 3.1 offset condition is
`1 + γᵢ^s ≤ ε < δᵢ^s` — the "+1" the plan added belongs ONLY on the lower endpoint — **verified for all
12 sub-subcones** (0 failures / ~250k points). All twelve formalized cores use these corrected intervals.
Aristotle independently confirmed the `𝒟₂⁻` and `𝒟₁⁻` cores (`tools/aristotle/st06_d{1,2}m_eo`).

**Remaining St06 (Tier 3):** Thms 3.3 / 3.4 (the binary `g=2` families, NOT covered by Thm 3.1) and
Cor 3.5 (Beatty unification of the Borwein–Bailey examples). See `PENDING_WORK.md`.

## Where it stands
**Three complete, axiom-clean layers** (every `#print axioms` = trust base `[propext, Classical.choice,
Quot.sound]`, zero custom axioms, zero `sorry`): (1) the **headline** (Graham–Pollak / √2) + the
**bonus** (Stoll [0902.4168] Thm 3.2's 7 pairs + Cor 3.3, with pair 5 resolved to its honest ε=½
content); (2) the **general #482 resolution** (Stoll [St05]: `erdos482_resolution`, any `w>0` any base
`g≥2`); (3) the **St06 fun-extension** (Acta Arith. 125): Example 1.1, Thm 3.1 (all 12 cones), Thm 3.3
(full), **Thm 3.4 full GENUINE symmetric interval** (`st06_thm34_{astep,closed,digits,isBit}_eps`,
corrected 2026-06-13 from the swapped-recurrence false "obstruction" — see Thm 3.4 entry above), and
**Cor 3.5 (the Beatty-unification capstone)**. Thm 3.4's printed interval is now machine-checked as a
**genuine t-universal theorem** (every `ε ∈ ½ ± (m−l+½)/D₁` works for all `w`), NOT the spurious
"only ε=½" the prior lap reported. What's left is optional polish (top-level showcase wiring).

## What's happened (newest first)
- **2026-06-13 (correction lap — Thm 3.4 genuine full interval)**: Harvested ON-LINE findings that the
  prior lap's Thm 3.4 "obstruction" formalized a **swapped recurrence** (`ε` on the b-step = Thm 3.3's
  placement; Stoll's 3.4 has `ε` on the a-step). Proved the GENUINE full symmetric interval as a real
  `t`-universal theorem: `st06_thm34_astep_eps` (a-step floor crux, every `ε∈½±(m−l+½)/D₁`, all `t∈[1,2)`,
  no Diophantine input) + `st06_thm34_{closed,digits,isBit}_eps`. Re-labeled the b-step "obstruction"
  theorems `[SWAPPED-VARIANT, NOT Thm 3.4]` (kept as documented contrast). All axiom-clean; build 🟢 8273.
- **2026-06-13 (review lap — Cor 3.5 capstone + Thm 3.4 obstruction [SUPERSEDED, see above])**: Two St06 closures + polish. (1)
  **Thm 3.4 full interval RESOLVED** (like pair 5): `st06_thm34_bstep_value` + `_bstep_band` (exact
  general-ε b-step + lands-iff-band) + `_band_fails_below/above_half` (machine-checked Diophantine
  obstruction — no ε≠½ is t-universal). (2) Polish: `isBit` corollaries for Thm 3.3/3.4 (GP diff ∈{0,1}),
  faithfulness certs `st06_cor35_recovers_gp` (r=1→√2) + `binDigit_three_sqrt2_first_four` (r=3→3√2).
  (3) Cubic exploration `notes/CUBIC-EXPLORATION.md` (negative: the trick doesn't extend to 2^{1/3}).
  All axiom-clean; 4 Aristotle cross-validations (engine/bstep_value/bstep_band confirmed from `crux`).
- **2026-06-13 (review lap — Cor 3.5 capstone)**: Closed **St06 Corollary 3.5** entirely, **without the
  PDF**. Reverse-engineered the exact statement numerically (`tools/sandbox/st06_cor35_*.py`): the GP
  recurrence from start `m` tracks `w(m)=r·α` (the Beatty real, `α∈{1+√2,1+1/√2}`, `m=⌊rα⌋`), reading
  off the binary digits of `r√2`. Built the digit engine = `gp_pair` generalized by a free factor `r`
  (`cor35_pair`, `cor35_pair_case2`, `cor35_floorA/B`, `cor35_base`), the capstone **`st06_cor35`** (via
  `beatty_unique_sqrt2`), and literal/bit forms (`st06_cor35_realDigits`, `st06_cor35_isBit`). All
  axiom-clean. **All St06 main theorems are now formalized**; the off-by-M PDF concern was illusory
  (Stoll's `w`-table = mantissa renormalization of the `r√2` digit string).
- **2026-06-07 (review/showcase lap)**: St06 online-fetch returned — unobtainable but off the critical
  path (harvested to `archive/findings/`; `ON-LINE-REQUEST.md` retired). Added (all axiom-clean):
  • **`erdos482_resolution_general_literal`** + `realDigits_mantissa_shift` (`Erdos482GeneralLiteral.lean`):
    closed the deliberately-left mantissa index-shift — the headline now reads off **any `w≥1`'s genuine
    `Real.digits w g i`** (at `n=i+m+2`, `m=⌊log_g w⌋`), not just the mantissa's.
  • `cor13_ternary_exp_one[_literal]` (`Cor13e.lean`, **base-3 digits of e** — the transcendental-in-odd-
    base object St06 is OEIS-tagged to; expansion `2.2011011212…₃` numerically verified).
  • **`gv_sqrt2_eq_u`** + `gp_sqrt2_digits_via_general[_literal]` (`GrahamPollakBridge.lean`): the general
    recurrence at Cor 1.1's `j=1` (`a=b=√2, ε=½`) is *literally* the original sequence `u`, so the general
    digit theorem re-proves √2 with a **machinery-disjoint** tree — original reads odd-index diffs
    (fractional digits `0,1,1,0,1,0,…`), general route reads even-index diffs (full `1.0110101…₂`).
  • `PROOF-JOURNEY.md` — process retrospective (the arc, methodology, instructive failures).
- **2026-06-06 (autonomous lap — pair-5 resolution + St05 start)**:
  • **Pair 5 RESOLVED** (full interval is not a theorem; honest content formalized): `stoll_pair5_closed_form`
    (typo-corrected §4 formula), `pair5_estep_band` (exact band characterization), `stoll_pair5_conditional`
    (conditional full-interval), `pair5_band_at_half` + `stoll_pair5_half_via_band` (band route to GP),
    `pair5_band_branch` + `pair5_band_fails_below_half`/`above_half` (precise obstruction). Diophantine infra:
    `fract_two_mul`, `fract_two_mul_branch`, `fract_sqrt2_pow_ne_half`, `sqrt2_pow_far_from_halfint`.
  • **St05 general track started** (`General/`): `Digits` (`digitStep`/`gdigit` range bounds +
    `realDigits_eq_digitStep` general Prop 2), `Thm13` (`thm13_digit_of_oddClosed`), `Mantissa`
    (`mantissa_mem`: 1≤t<g). Thm 1.3 numerically verified (g∈{2,3,10}, w∈{√2,√3,π}). All axiom-clean.
- **2026-06-06 (review lap, late)**: Pair-5 deep dive. Added `vv_eq_u_of_evenstep` /
  `stoll_pair5_of_evenstep` (pair 5 reduced to one hypothesis `Heven`; axiom-clean) and
  `sqrt2_badly_approximable` (`1/(3q)≤|q√2−p|`, Aristotle-proved, kernel-verified). **CORRECTION**:
  numerics show the `vv ε = u` model is a dead end — interior ε in the claimed pair-5 interval diverge
  from √2's digits at n=452. Pair 5 now blocked on the `ON-LINE-REQUEST` (interval may be wrong). The
  three lemmas are correct/axiom-clean but cover only ε=½. See PENDING_WORK §1.
- **2026-06-06 (review lap, cont.)**: `stoll_gp_isBit` — **master theorem**: GP difference ∈ {0,1}
  for ε in any of the 7 proven pair intervals (k≥31). `vv_one_le_and_mono` (Aristotle-proved,
  kernel-verified). Pinned pair 5 as the lone gap: numerics show `vv ε = u` on `[ξ₁,ξ₂)` but the
  step-margin shrinks (1.4e-6 at n=1811) → genuinely Diophantine, NOT finite (filed ON-LINE-REQUEST).
- **2026-06-06 (review lap)**: Completed Theorem 3.2 for pairs 1–4,6,7,8 over full intervals.
  • `stoll_pair6` + `stoll_pair6_t`: pair 6 for the *whole* interval `[1296121037√2/2−916495974,
    79109√2/2−55938)` via `cor33_base_interval` (the two endpoint-defining steps 30/58 are exactly
    tight; close because the √2-coefficient of the exact product bounds cancels to 0). • Verbatim
    `tᵢ`-form restatements `stoll_pair{1,2,3,4,7,8}_t` + `cor33_unconditional_t` (digits of `tᵢ`, not
    just `αᵢ√2`). • `stoll_endpoints_strictMono` + `stoll_intervals_cover` (disjoint-and-cover). All
    axiom-clean. Characterized pair 5's invariant `P5/Q5` numerically (next thread).
- **2026-06-06 (prior lap)**: Took the bonus from "paper-blocked" to complete & axiom-clean —
  `stoll_pair`/`stoll_digit` general core, pairs 1–4,7,8, `cor33_unconditional` (title result),
  `binDigit_div_pow` (tᵢ bridge), via the cleaner α√2-only invariant + interior-ε trick for Cor 3.3.
- **earlier**: Headline `graham_pollak` + digit-bridge to mathlib `Real.digits`, irrationality /
  non-termination corollaries, `u_pos`/`u_strictMono`.

## Outstanding
### Short-term (mirror PENDING_WORK top)
- **No open mathematical items.** All St06 main theorems formalized & axiom-clean; **Thm 3.4's full
  symmetric interval is now a genuine t-universal theorem** (`st06_thm34_digits_eps`, corrected this lap
  from the swapped-recurrence false obstruction).
- **Optional polish**: wire `st06_cor35`/`erdos482_resolution` into a single top-level St06 showcase;
  unified Thm 3.3/3.4/Cor 3.5 `isBit` master; concrete `r=2`→digits-of-`2√2` certificate for Cor 3.5;
  retire the swapped `_bstep_*` theorems entirely (currently kept as documented contrast).
### Long-term
- "Generalize to other algebraic numbers" — Stoll [St05] already resolves it elementarily (DONE as
  `erdos482_resolution`); deeper generalizations (cubic irrationals, etc.) would need new math.
### To completion
- The headline + Thm 3.2 (7 pairs) + Cor 3.3 + St05 general (`erdos482_resolution`) + St06 (Ex 1.1,
  Thm 3.1/3.3/3.4 [full genuine interval], Cor 3.5) are all done & **axiom-clean**. Nothing on the
  critical path open.

## Axiom ledger
All headline theorems verified `#print axioms` this lap = trust base only; **0 math axioms** (🟢).
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `graham_pollak` | uncond (digits of √2) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean — no machinery |
| `cor33_unconditional` (+ `_t`) | uncond (digits of 759250125√2) | trust base | 🟢 clean |
| `erdos482_resolution` | uncond (St05: any `w>0`, any base `g≥2`) | trust base | 🟢 clean |
| `st06_example11_ternary_e` | uncond (St06 Ex 1.1, base-3 digits of e) | trust base | 🟢 clean |
| `st06_thm31_d{1..6}{m,p}_digits` | uncond (St06 Thm 3.1, all 12 cones) | trust base | 🟢 clean |
| `st06_thm33_digits` (+ `_grahampollak`) | uncond (St06 Thm 3.3, full ε-interval) | trust base | 🟢 clean |
| `st06_thm34_digits_eps` (+ `_astep_eps`, `_closed_eps`, `_isBit_eps`) | St06 Thm 3.4, GENUINE full symmetric ε-interval (t-universal) | trust base | 🟢 clean |
| `st06_thm34_bstep_band` / `_band_fails_below/above_half` | ⚠️ SWAPPED-VARIANT (ε on b-step = Thm 3.3 placement), NOT Thm 3.4 | trust base | 🟢 clean Lean, unfaithful statement |
| `st06_cor35` (+ `_realDigits`, `_isBit`) | uncond (St06 Cor 3.5, Beatty unification) | trust base | 🟢 clean |
| `selfref_crux_solvable_iff` (+ `_fails_of_three_le`, `_offset_unique`) | NEW: self-ref digit crux solvable iff g=2, and then offset c=½ is forced | trust base | 🟢 clean |
| `onefloor_div2_crux_solvable_iff` (+ `_crux_solvable`, `_crux_cbrt2`, `_offset_unique`) | NEW: single-floor /2 crux (mult β, free base 2) solvable ⇔ β<2 (c=½ forced); **refutes findings-doc "Tier-1" cubic impossibility** — cubic 2^{1/3} single floor IS solvable, obstruction is purely multi-floor | trust base | 🟢 clean |
| `cubic_threestep_defect` (+ `cubic_combined_defect_range_wide{,_cbrt2}`) | NEW (Tier-2 core): exact 3-step cubic defect identity `v₃=2u+C−(α²f₁+αf₂+f₃)`; combined two-floor defect spans width α²+α+1>1 ⇒ fits no width-1 window. Localizes cubic obstruction to the two internal floors; unconditional impossibility hinges on (open) `{α^n ξ}` equidistribution — see PENDING_WORK ★ | trust base | 🟢 clean |

No 🟡/🟠/🔴 axioms anywhere: the whole development is elementary (floors, √2, π/e bounds, Rayleigh from
mathlib). Thm 3.4's full k-dependent interval — once mis-formalized as a Diophantine "obstruction" — is
now proven as a genuine `t`-universal theorem (`st06_thm34_digits_eps`): `ε` sits on the a-step, whose
floor bracket is uniform over `t`, so Stoll's printed symmetric interval holds for every `w`. No open
axiom anywhere.

## Pointers
`HANDOFF.md` (completion pointer) · session batons archived in `archive/handoff/` ·
`NOTES-FOR-STOLL.md` (pair-5 errata + computations) · `PENDING_WORK.md` (historical) ·
paper transcription: `archive/findings/ON-LINE-FINDINGS-2026-06-06-stoll-thm32-cor33.md`
