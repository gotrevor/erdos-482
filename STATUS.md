# STATUS — erdos-482 📊

**Stoll's binary-digits-of-759250125√2 (generalizes Graham–Pollak / Erdős #482), formalized in Lean 4.** · **Build**: 🟢 green (8255 jobs) · **Updated**: review lap · 2026-06-06 · `adbd69d`

## Where it stands
The **headline** (Graham–Pollak: the GP sequence reads off the binary digits of √2) and the **bonus**
(Stoll's Theorem 3.2 + Corollary 3.3) are both complete and **axiom-clean** (every headline theorem's
`#print axioms` = the trust base `[propext, Classical.choice, Quot.sound]`, zero custom axioms). This
review lap closed the last open *math* thread: **pair 6 now holds for its full ε-interval** (not just
the Cor-3.3 ε), so **Theorem 3.2 is complete for all 7 non-special pairs over their whole intervals**,
each also stated in the paper's **verbatim `tᵢ` form**, plus a **completeness** theorem (the 8
intervals are disjoint and exactly cover `[1−√2/2, √2/2)`). The one remaining gap is **pair 5** (the
special β=0 / `t=√2` case): proved at ε=½ by the headline, but its full-interval *vv*-based version
needs a non-uniform ε-step analysis (see Outstanding).

## What's happened (newest first)
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
