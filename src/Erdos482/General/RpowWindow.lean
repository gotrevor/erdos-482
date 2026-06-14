import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-!
# General degree-`d` partial-defect window width `> 2`

**Context (the general-`d` self-referential frontier).**  In the cubic/quartic impossibilities the
combined internal-floor defect `g = α^{d-1}f₁ + α^{d-2}f₂ + … + α f_{d-1}` (with `α = 2^{1/d}`,
`fᵢ ∈ [0,1)`) ranges over `[0, S_d)` with `S_d = α + α² + … + α^{d-1}`.  A base-2 digit forces
`g` into a window of width `2`; the impossibility is driven by `S_d > 2`, so a dense orbit of
`(f₁,…,f_{d-1})` must leave the window.  (`cubic_combined_defect_range_wide` is the `d = 3` instance.)

**This file proves the width brick uniformly for every `d ≥ 3`** (`rrt_window_gt_two`).  The clean
pivot is the closed form: since `α^d = 2`, the geometric sum gives `S_d = 1/(α-1) − 1 = (2-α)/(α-1)`,
and `S_d > 2 ⟺ α < 4/3 ⟺ 2 < (4/3)^d`, which holds for all `d ≥ 3` because `(4/3)³ = 64/27 > 2` and
`(4/3)^d` is increasing.  (For `d = 2`, `α = √2 ≈ 1.41 > 4/3`, `S_2 = √2 < 2` — consistent with the
original Graham–Pollak `√2` recurrence being solvable: the obstruction begins exactly at `d = 3`.)

Everything here depends only on the trust base `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos482.General

open Finset

/-- **`2^{1/d} < 4/3` for `d ≥ 3`.**  Equivalent to `2 < (4/3)^d`, which holds because `(4/3)³ = 64/27
> 2` and `n ↦ (4/3)ⁿ` is increasing.  This is the analytic pivot for the width bound: the partial
defect window has width `> 2` precisely when `α < 4/3`. -/
theorem rrt_lt_four_thirds (d : ℕ) (hd : 3 ≤ d) : (2 : ℝ) ^ ((1 : ℝ) / d) < 4 / 3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hdinv : (0 : ℝ) < (1 : ℝ) / d := div_pos one_pos hd0
  -- `2 < (4/3)^d`.
  have hpow : (2 : ℝ) < (4 / 3) ^ d := by
    have h3 : ((4 : ℝ) / 3) ^ 3 ≤ (4 / 3) ^ d := pow_le_pow_right₀ (by norm_num) hd
    have h64 : ((4 : ℝ) / 3) ^ 3 = 64 / 27 := by norm_num
    linarith [h3, h64]
  -- raise to the `1/d` power (strictly increasing on positives).
  have hlt := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 2) hpow hdinv
  have hrhs : ((4 / 3 : ℝ) ^ d) ^ ((1 : ℝ) / d) = 4 / 3 := by
    rw [← Real.rpow_natCast (4 / 3 : ℝ) d, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
      mul_one_div, div_self hdne, Real.rpow_one]
  rwa [hrhs] at hlt

/-- **The partial-defect window width exceeds `2` for every `d ≥ 3`** (`α = 2^{1/d}`):
`2 < α + α² + … + α^{d-1}`.  The general-`d` analogue of `cubic_combined_defect_range_wide`.  Proof:
`α^d = 2`, the geometric sum collapses to `1/(α-1) − 1`, and `1/(α-1) − 1 > 2 ⟺ α < 4/3`
(`rrt_lt_four_thirds`). -/
theorem rrt_window_gt_two (d : ℕ) (hd : 3 ≤ d) :
    (2 : ℝ) < ∑ j ∈ Finset.Ico 1 d, ((2 : ℝ) ^ ((1 : ℝ) / d)) ^ j := by
  set α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / d) with hα
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hαpos : 0 < α := Real.rpow_pos_of_pos (by norm_num) _
  have hαd : α ^ d = 2 := by
    rw [hα, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / d)) d,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hdne, Real.rpow_one]
  -- `α > 1` (else `α^d ≤ 1 < 2`).
  have hα1 : 1 < α := by
    by_contra hc
    have hle : α ≤ 1 := not_lt.mp hc
    have : α ^ d ≤ 1 ^ d := pow_le_pow_left₀ hαpos.le hle d
    rw [hαd, one_pow] at this; linarith
  have hαlt : α < 4 / 3 := rrt_lt_four_thirds d hd
  have hpos : 0 < α - 1 := by linarith
  -- geometric sum over `Ico 1 d`: `∑_{1≤j<d} αʲ = (αᵈ - α¹)/(α-1) = (2-α)/(α-1)`.
  rw [geom_sum_Ico (by linarith : α ≠ 1) (show 1 ≤ d by omega), hαd, pow_one]
  -- `2 < (2-α)/(α-1) ⟺ 2(α-1) < 2-α ⟺ α < 4/3`.
  rw [lt_div_iff₀ hpos]
  linarith

end Erdos482.General
