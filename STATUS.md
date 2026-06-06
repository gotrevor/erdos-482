# STATUS — erdos-482 📊

**Stoll's binary-digits-of-759250125√2 (generalizes Graham–Pollak / Erdős #482), formalized in Lean 4.** · **Build**: 🟢 green (8265 jobs) · **Updated**: 2026-06-06 (**ENTIRE St05 paper formalized — #482 resolved for any w>0, any base g≥2**)

## 🏆 St05 COMPLETE — Erdős #482 resolved in full generality (2026-06-06)
The whole of Stoll [St05] is now machine-checked and **axiom-clean** (`src/Erdos482/General/`):
**Thm 1.1** (Rabinowitz–Gilbert, `Thm11.lean`), **Thm 1.2 Case I** (ε-interval `[1/3,2/3)`, `Thm12CaseI.lean`)
+ **Case II** (ε=½, `Thm12.lean`), **Thm 1.3** (g-ary, any base — the headline, `Thm13Closed.lean`:
`thm13_closed`+`thm13_digits`), **Cor 1.1** (both √2 binary families, `Cor11.lean`), **Cor 1.2** (ternary
√2, `Cor12.lean`), **Prop 2** (`Digits.lean`). Top-level packaging: **`erdos482_resolution`**
(`Erdos482General.lean`) — for any `w>0`, any `g≥2`, an explicit recurrence reads off `w`'s base-`g`
digits. The joint-induction obligation the stalled Aristotle job `e0240fef` couldn't crack was proved
locally. Every declaration `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
Next frontier: **St06** (Acta Arith. 2006, sharper) — needs online fetch (see `ON-LINE-REQUEST.md`).

## Where it stands
The **headline** (Graham–Pollak: the GP sequence reads off the binary digits of √2) and the **bonus**
(Stoll's Theorem 3.2 + Corollary 3.3) are complete and **axiom-clean** (every theorem's `#print axioms`
= the trust base `[propext, Classical.choice, Quot.sound]`, zero custom axioms, zero `sorry`).
**Pair 5 is now resolved**: the online findings established that Stoll's full-interval claim is *not a
theorem* (false at the stated endpoint, fails at n=280); only ε=½ works for all n (= the headline).
The honest content was formalized: the typo-corrected closed form, an exact **band characterization**
of the ε-step, the **conditional** full-interval theorem, and the **precise obstruction** (both sides)
showing why no ε≠½ is uniformly admissible (PENDING_WORK §1, all axiom-clean).
A new **general track** (Stoll [St05], the real #482 resolution for any `w>0`, any base `g≥2`) is
underway in `src/Erdos482/General/` (PENDING_WORK §1b): the g-ary digit bound, Prop-2 bridge to
mathlib `Real.digits`, the mantissa lemma, and Thm 1.3's conclusion modulo the closed-form induction
(the induction is grinding on Aristotle, job `e0240fef`).

## What's happened (newest first)
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
- **Pair 5 full-interval** (`t₅=√2`, special β=0): the only pair without a vv-based interval theorem.
  Invariant (verified): `vv(2j+1)=⌊√2·2^j⌋+2^j`, `vv(2j+2)=⌊√2·2^j⌋+2^{j+1}`; digit
  `vv(2k+1)−2vv(2k−1)=binDigit √2 k`. The ½-step is `eq8_general(ε=½)`; the ε-step bracket
  `{x}−√2{x/2}+√2ε` is **non-uniform in x** (uniform only at ε=½) — needs a dedicated bound.
- **Master theorem**: once pair 5 lands, a single `∀ ε admissible, ∀ k≥31, vv ε (2k+1)−2vv ε (2k−1) ∈
  {0,1}` via `stoll_intervals_cover` + the 8 pairs.
### Long-term
- "Generalize to other algebraic numbers" — open research direction, needs new math.
### To completion
- The headline + Theorem 3.2 (7 pairs) + Cor 3.3 are done & axiom-clean. "Done" for the full bonus =
  add pair 5's interval + the master theorem; then every result's base is trust-base only.

## Axiom ledger
All headline theorems verified `#print axioms` this lap = trust base only; **0 math axioms** (🟢).
| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `graham_pollak` | uncond (digits of √2) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean — no machinery |
| `stoll_digit`, `stoll_pair` | uncond (Thm 3.2 core) | trust base | 🟢 clean |
| `stoll_pair1..4,6,7,8` (+ `_t`) | uncond (Thm 3.2, 7 pairs, full intervals) | trust base | 🟢 clean |
| `cor33_unconditional` (+ `_t`) | uncond (digits of 759250125√2) | trust base | 🟢 clean |
| `stoll_intervals_cover` | uncond (intervals partition range) | trust base | 🟢 clean |
| `stoll_gp_isBit` | uncond (GP diff is a bit, 7 pairs) | trust base | 🟢 clean |
| `vv_one_le_and_mono` | structural (vv ≥1, monotone) | trust base | 🟢 clean |

No 🟡/🟠/🔴 axioms anywhere: the whole development is elementary (floors, √2, π/e bounds from mathlib).
The remaining work (pair 5, master theorem) is *new proof*, not axiom discharge.

## Pointers
ROADMAP: (none — see this file) · newest HANDOFF: `HANDOFF-2026-06-06-1946.md` (+ this lap's) ·
`PENDING_WORK.md` (attack paths) · paper transcription: `archive/findings/ON-LINE-FINDINGS-2026-06-06-stoll-thm32-cor33.md`
