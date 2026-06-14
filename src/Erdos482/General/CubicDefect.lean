import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

end Erdos482.General
