import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational

/-!
# The cubic three-step defect identity — where the cubic obstruction actually lives

**Context.**  `Erdos482.crux` makes the Graham–Pollak two-step `√2`-map a clean multiply-by-2 shift:
the single internal floor's rounding error stays in a width-1 window, uniformly in `x`.  The natural
cubic analogue replaces `√2` by `α = 2^{1/3}` (`α³ = 2`) and uses a **three**-step map with a
3-periodic offset schedule `(c₀,c₁,c₂)`:
`v₁ = ⌊α(u+c₀)⌋`, `v₂ = ⌊α(v₁+c₁)⌋`, `v₃ = ⌊α(v₂+c₂)⌋`.  For this to read base-2 digits, the
three-fold composite must be a clean shift `v₃ = 2u + (digit)` for all `u` along the orbit.

**This file proves the exact algebraic identity governing that composite** (`cubic_threestep_defect`):

> `v₃ = 2u + (2c₀ + α²c₁ + αc₂) − (α²·f₁ + α·f₂ + f₃)`,
> where `f₁ = {α(u+c₀)}`, `f₂ = {α(v₁+c₁)}`, `f₃ = {α(v₂+c₂)}` are the three internal floor errors.

It is pure algebra (the only input is `α³ = 2`).  Its payoff is to **localize the cubic wall precisely**:

* The "digit" produced is `v₃ − 2u = (2c₀+α²c₁+αc₂) − (α²f₁ + α·f₂ + f₃)`.
* For a base-2 readout this must lie in `{0,1}` for **every** `u` on the orbit, i.e. the **combined
  defect** `α²f₁ + α·f₂ + f₃` must stay inside a *single* width-1 window `(2c₀+α²c₁+αc₂) − {0,1}`.
* But `f₁,f₂,f₃ ∈ [0,1)` independently, so `α²f₁ + α·f₂ + f₃` ranges over `[0, α²+α+1) ≈ [0, 4.05)`
  — width `α²+α+1 > 1` (`cubic_combined_defect_range_wide`).  **Two internal floors give a defect
  spread far exceeding 1**, unlike the single-floor `√2` case whose spread is exactly 1.

So the cubic obstruction is **not** at any single-floor level (cf.
`SelfRefWall.onefloor_div2_crux_cbrt2`, where the single floor *is* solvable): it is forced by the
**two** internal floors of the three-step composite, whose errors `(f₁,f₂,f₃)` cannot be simultaneously
pinned into a width-1 window by any fixed offset schedule once the orbit explores their full range.
Whether the geometric orbit `u_n ≈ W·2^{n/3}` actually realises that full range is the residual
(equidistribution-of `{α^n ξ}`) question — see `notes/CUBIC-EXPLORATION.md` and `PENDING_WORK.md`.
-/

namespace Erdos482.General

open Real

/-- **The cubic three-step defect identity.**  For any `α` with `α³ = 2`, offsets `c₀ c₁ c₂` and start
`u`, the three-step floor map `v₁ = ⌊α(u+c₀)⌋`, `v₂ = ⌊α(v₁+c₁)⌋`, `v₃ = ⌊α(v₂+c₂)⌋` satisfies
`v₃ = 2u + (2c₀ + α²c₁ + αc₂) − (α²·{α(u+c₀)} + α·{α(v₁+c₁)} + {α(v₂+c₂)})`.
The composite is a clean shift-by-2 exactly modulo the *combined internal-floor defect*
`α²·f₁ + α·f₂ + f₃`.  Pure algebra from `α³ = 2`. -/
theorem cubic_threestep_defect (α u c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) :
    let v1 : ℝ := (⌊α * (u + c0)⌋ : ℤ)
    let v2 : ℝ := (⌊α * (v1 + c1)⌋ : ℤ)
    let v3 : ℝ := (⌊α * (v2 + c2)⌋ : ℤ)
    v3 = 2 * u + (2 * c0 + α ^ 2 * c1 + α * c2)
        - (α ^ 2 * Int.fract (α * (u + c0)) + α * Int.fract (α * (v1 + c1))
            + Int.fract (α * (v2 + c2))) := by
  intro v1 v2 v3
  have h1 : v1 = α * (u + c0) - Int.fract (α * (u + c0)) := (Int.self_sub_fract _).symm
  have h2 : v2 = α * (v1 + c1) - Int.fract (α * (v1 + c1)) := (Int.self_sub_fract _).symm
  have h3 : v3 = α * (v2 + c2) - Int.fract (α * (v2 + c2)) := (Int.self_sub_fract _).symm
  linear_combination h3 + α * h2 + α ^ 2 * h1 + (u + c0) * hα

/-- **The combined two-floor defect does not fit any width-1 window** (for any `α > 1`).  As
`(f₁,f₂,f₃)` ranges over `[0,1)³`, the combined defect `α²·f₁ + α·f₂ + f₃` cannot be confined to a
closed interval `[C, C+1]` of length 1.  Witnesses: `(0,0,0) ↦ 0` and `(½,½,½) ↦ (α²+α+1)/2`, which
already differ by more than 1 since `α²+α > 1`.

Combined with `cubic_threestep_defect` (the "digit" is `v₃ − 2u = (2c₀+α²c₁+αc₂) − (defect)`, which
must lie in `{0,1} ⊆` a width-1 window for a base-2 readout), this is the precise structural reason
the cubic three-step map has **no** universally-valid fixed offset schedule: two internal floors give a
defect spread `> 1`.  Contrast `SelfRefWall.onefloor_div2_crux_solvable` — one internal floor gives
spread *exactly* 1, which fits.  (The residual question is whether the geometric orbit realises both
witness configurations; see `PENDING_WORK.md`.) -/
theorem cubic_combined_defect_range_wide (α : ℝ) (hα1 : 1 < α) :
    ¬ ∃ C : ℝ, ∀ f1 f2 f3 : ℝ, 0 ≤ f1 → f1 < 1 → 0 ≤ f2 → f2 < 1 → 0 ≤ f3 → f3 < 1 →
      α ^ 2 * f1 + α * f2 + f3 ∈ Set.Icc C (C + 1) := by
  rintro ⟨C, hC⟩
  have h0 := hC 0 0 0 le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num)
  have hh := hC (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [Set.mem_Icc] at h0 hh
  -- h0 : C ≤ 0 ∧ 0 ≤ C+1 ;  hh.2 : α²/2+α/2+1/2 ≤ C+1 ;  with α>1 ⇒ α²+α>2, contradiction
  nlinarith [h0.1, h0.2, hh.1, hh.2, hα1, mul_pos (show (0:ℝ) < α by linarith) (show (0:ℝ) < α by linarith)]

/-- The cubic obstruction is base-`2`, multiplier `2^{1/3}`: the combined two-floor defect for
`α = 2^{1/3}` does not fit any width-1 window. -/
theorem cubic_combined_defect_range_wide_cbrt2 :
    ¬ ∃ C : ℝ, ∀ f1 f2 f3 : ℝ, 0 ≤ f1 → f1 < 1 → 0 ≤ f2 → f2 < 1 → 0 ≤ f3 → f3 < 1 →
      ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * f1 + (2 : ℝ) ^ ((1 : ℝ) / 3) * f2 + f3
        ∈ Set.Icc C (C + 1) := by
  apply cubic_combined_defect_range_wide
  have h : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  rwa [Real.rpow_zero] at h

/-- The three-step cubic orbit value `v₃ = ⌊α(⌊α(⌊α(u+c₀)⌋+c₁)⌋+c₂)⌋` from an integer start `u`. -/
noncomputable def cubicV3 (α c0 c1 c2 : ℝ) (u : ℤ) : ℤ :=
  ⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋

/-- The combined internal-floor defect `α²·f₁ + α·f₂ + f₃` of the three-step cubic map at start `u`. -/
noncomputable def cubicDefect (α c0 c1 c2 : ℝ) (u : ℤ) : ℝ :=
  α ^ 2 * Int.fract (α * ((u : ℝ) + c0))
    + α * Int.fract (α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
    + Int.fract (α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2))

/-- Bridge: the extracted "digit" `cubicV3 − 2u` equals the schedule constant minus the combined
defect, `(2c₀+α²c₁+αc₂) − cubicDefect`.  Restatement of `cubic_threestep_defect` on integer starts. -/
theorem cubicV3_sub_eq (α c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) (u : ℤ) :
    ((cubicV3 α c0 c1 c2 u : ℤ) : ℝ) - 2 * (u : ℝ)
      = (2 * c0 + α ^ 2 * c1 + α * c2) - cubicDefect α c0 c1 c2 u := by
  have hd := cubic_threestep_defect α (u : ℝ) c0 c1 c2 hα
  simp only [cubicV3, cubicDefect]
  linarith [hd]

/-- **Conditional cubic impossibility (the honest ceiling).**  Fix `α` with `α³ = 2` and any offset
schedule `(c₀,c₁,c₂)`.  *If* the orbit realises two starts `u, u'` whose combined internal-floor
defects differ by more than `1`, *then* the two extracted digits `cubicV3 − 2u` and `cubicV3' − 2u'`
cannot both be base-2 digits (`∈ {0,1}`) — so no such schedule reads base-2 digits along an orbit that
explores a wide defect pair.  This packages exactly "the cubic three-step map fails *modulo* the orbit
realising the wide defect spread of `cubic_combined_defect_range_wide`"; whether the geometric orbit
`u_n ≈ W·α^n` does realise such a pair is the residual equidistribution question (OPEN for fixed `ξ`;
see `PENDING_WORK.md` ★).  Proof: the two digits differ (as reals) by exactly the defect difference,
`> 1`, but two elements of `{0,1}` differ by at most `1`. -/
theorem cubic_threestep_digit_pair_fails (α c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) (u u' : ℤ)
    (hwide : 1 < |cubicDefect α c0 c1 c2 u - cubicDefect α c0 c1 c2 u'|) :
    ¬ ((cubicV3 α c0 c1 c2 u - 2 * u = 0 ∨ cubicV3 α c0 c1 c2 u - 2 * u = 1)
        ∧ (cubicV3 α c0 c1 c2 u' - 2 * u' = 0 ∨ cubicV3 α c0 c1 c2 u' - 2 * u' = 1)) := by
  rintro ⟨hb, hb'⟩
  -- the two real digit-values differ by exactly the defect difference
  have e := cubicV3_sub_eq α c0 c1 c2 hα u
  have e' := cubicV3_sub_eq α c0 c1 c2 hα u'
  have hreal : 1 < |((cubicV3 α c0 c1 c2 u : ℝ) - 2 * u) - ((cubicV3 α c0 c1 c2 u' : ℝ) - 2 * u')| := by
    have : ((cubicV3 α c0 c1 c2 u : ℝ) - 2 * u) - ((cubicV3 α c0 c1 c2 u' : ℝ) - 2 * u')
        = cubicDefect α c0 c1 c2 u' - cubicDefect α c0 c1 c2 u := by rw [e, e']; ring
    rw [this, abs_sub_comm]; exact hwide
  -- but both integer digits are in {0,1}, so the real gap is ≤ 1
  have hcast : ((cubicV3 α c0 c1 c2 u : ℝ) - 2 * u) - ((cubicV3 α c0 c1 c2 u' : ℝ) - 2 * u')
      = (((cubicV3 α c0 c1 c2 u - 2 * u) - (cubicV3 α c0 c1 c2 u' - 2 * u') : ℤ) : ℝ) := by
    push_cast; ring
  rw [hcast] at hreal
  rcases hb with h | h <;> rcases hb' with h' | h' <;> rw [h, h'] at hreal <;> norm_num at hreal

/-- **The precise reduction to equidistribution (positive form).**  If the three-step cubic map reads
base-2 digits at two starts `u, u'` — i.e. both digits `cubicV3 − 2u`, `cubicV3' − 2u'` are in `{0,1}`
— then the two combined defects differ by at most `1`.  Equivalently: a schedule that reads base-2
digits along an orbit forces *all* the orbit's combined defects into a single width-1 window.  Since the
defect *range* is `α²+α+1 > 1` (`cubic_combined_defect_range_wide`), the obstruction is exactly that the
orbit must avoid exploring that full range — the (open, for fixed `ξ`) `{α^n ξ}` equidistribution
question.  This is the clean statement to chain a future equidistribution lemma against. -/
theorem cubic_valid_digits_defects_close (α c0 c1 c2 : ℝ) (hα : α ^ 3 = 2) (u u' : ℤ)
    (hu : cubicV3 α c0 c1 c2 u - 2 * u = 0 ∨ cubicV3 α c0 c1 c2 u - 2 * u = 1)
    (hu' : cubicV3 α c0 c1 c2 u' - 2 * u' = 0 ∨ cubicV3 α c0 c1 c2 u' - 2 * u' = 1) :
    |cubicDefect α c0 c1 c2 u - cubicDefect α c0 c1 c2 u'| ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  exact cubic_threestep_digit_pair_fails α c0 c1 c2 hα u u' hgt ⟨hu, hu'⟩

/-- `2^{1/3}` is irrational — the base prerequisite for any equidistribution argument on this frontier
(e.g. attack-path #2 in `PENDING_WORK.md`: density/equidistribution of the first internal-floor error
`{α·u}` over integers needs `α` irrational; the full obstruction needs the stronger, open
fixed-`ξ` equidistribution of `{α^n ξ}`). -/
theorem irrational_cbrt_two : Irrational ((2 : ℝ) ^ ((1 : ℝ) / 3)) := by
  have hx3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h1 : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    rwa [Real.rpow_zero] at h
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) < 2 := by
    have h : (2 : ℝ) ^ ((1 : ℝ) / 3) < (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    rwa [Real.rpow_one] at h
  refine irrational_nrt_of_notint_nrt 3 2 (by push_cast; exact hx3) ?_ (by norm_num)
  rintro ⟨y, hy⟩
  rw [hy] at h1 h2
  have : (1 : ℤ) < y := by exact_mod_cast h1
  have : y < (2 : ℤ) := by exact_mod_cast h2
  omega

/-- **The block orbit is a base-2 expansion** (`⌊W·2ⁿ⌋`), not geometric base-`α`.  If the three-step
cubic map reads valid base-2 digits along an orbit — `orbit (n+1) = cubicV3 (orbit n)` with every digit
`cubicV3 − 2·orbit ∈ {0,1}` — then `2ⁿ·orbit₀ ≤ orbit n ≤ 2ⁿ·orbit₀ + (2ⁿ − 1)`, i.e.
`orbit n = ⌊W·2ⁿ⌋` for `W = orbit₀ + 0.d₀d₁… ∈ [orbit₀, orbit₀+1)`.

**Why this matters (corrects an earlier mischaracterisation).**  The block recurrence is
`u_{n+1} = 2u_n + dₙ`, so the orbit **doubles per block** — `uₙ ≍ W·2ⁿ`, NOT `W·α^n`.  Hence the first
internal-floor error is `f₁ = {α(uₙ+c₀)} ≈ {(αW)·2ⁿ + …}` — a **doubling-map** orbit, so the residual
obstruction is the **base-2 normality of `αW`** (Borel: a.e. real is normal), not the geometric
`{α^n ξ}` equidistribution.  Base-2 normality is the standard, correct frame for attack-path #2
(almost-all-`W`); mathlib does not yet have Borel's normal-number theorem, so that is the infrastructure
to build/port.  (HOSTCHECK: the surviving schedule's `uₙ/2ⁿ → 1.24987 = W`, matching `cubic_recover.py`.) -/
theorem cubic_block_orbit_base_two_bounds (α c0 c1 c2 : ℝ) (orbit : ℕ → ℤ)
    (hstep : ∀ n, orbit (n + 1) = cubicV3 α c0 c1 c2 (orbit n))
    (hbit : ∀ n, cubicV3 α c0 c1 c2 (orbit n) - 2 * orbit n = 0
        ∨ cubicV3 α c0 c1 c2 (orbit n) - 2 * orbit n = 1) :
    ∀ n, 2 ^ n * orbit 0 ≤ orbit n ∧ orbit n ≤ 2 ^ n * orbit 0 + (2 ^ n - 1) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have h2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h3 : (2 : ℤ) ^ (k + 1) * orbit 0 = 2 * (2 ^ k * orbit 0) := by rw [h2]; ring
    have hval : cubicV3 α c0 c1 c2 (orbit k)
        = 2 * orbit k + (cubicV3 α c0 c1 c2 (orbit k) - 2 * orbit k) := by ring
    rw [hstep k, hval]
    rcases hbit k with hd | hd <;> rw [hd] <;> omega

end Erdos482.General
