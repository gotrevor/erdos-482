import Erdos482.General.Thm13Closed

/-!
# Stoll [St05] Corollary 1.2 — ternary digits of √2 (instantiation of Theorem 1.3)

A concrete showcase of the unconditional general theorem `thm13_digits` at base `g = 3`, `w = √2`.
Stoll's coefficients are `a = (9 − 3√2)/14`, `b = 6 + 2√2` (one checks `a = 3/((3−1)(√2+3))` and
`b = (3−1)(√2+3)`, so `a·b = 3`).  Since `1 ≤ √2 < 3` the mantissa is `t = √2` itself (`m = 0`), so
the recurrence's Graham–Pollak difference reads off the **ternary** digits of `√2 = (1.102011221…)₃`.
Any offset `ε ∈ [−1/3, 4/3)` works; we take `ε = 0`.

Axiom-clean (inherits `thm13_digits`'s `[propext, Classical.choice, Quot.sound]`).
-/

namespace Erdos482.General

open Real

private lemma sqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 :=
  le_of_lt ((Real.lt_sqrt (by norm_num)).mpr (by norm_num))

private lemma sqrt2_lt_three : Real.sqrt 2 < 3 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- **St05 Corollary 1.2.**  The recurrence `gu 3 ((9−3√2)/14) (6+2√2) 0` extracts the ternary
digits of `√2`: for every `n ≥ 1`, `gu(2n) − 3·gu(2n−2)` equals the base-`3` digit
`Real.digits (√2·3^{n−1}/3) 3 0`. -/
theorem cor12_ternary_sqrt2 (n : ℕ) (hn : 1 ≤ n) :
    gu 3 ((9 - 3 * Real.sqrt 2) / 14) (6 + 2 * Real.sqrt 2) 0 (2 * n)
        - 3 * gu 3 ((9 - 3 * Real.sqrt 2) / 14) (6 + 2 * Real.sqrt 2) 0 (2 * n - 2)
      = ((Real.digits (Real.sqrt 2 * (3 : ℝ) ^ (n - 1) / 3) 3 0 : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 + 3 := by have := sqrt2_ge_one; linarith
  -- a = 3/((3−1)(√2+3))
  have ha : (9 - 3 * Real.sqrt 2) / 14
      = (3 : ℝ) / (((3 : ℝ) - 1) * (Real.sqrt 2 + 3)) := by
    rw [div_eq_div_iff (by norm_num) (by positivity)]
    nlinarith [h2]
  -- b = (3−1)(√2+3)
  have hb : (6 + 2 * Real.sqrt 2) = ((3 : ℝ) - 1) * (Real.sqrt 2 + 3) := by ring
  exact thm13_digits 3 (by norm_num) (Real.sqrt 2) sqrt2_ge_one sqrt2_lt_three
    0 ((9 - 3 * Real.sqrt 2) / 14) (6 + 2 * Real.sqrt 2) ha hb
    (by norm_num) (by norm_num) n hn

/-- **Cor 1.2, literal-digit form.**  For `n ≥ 2`, the ternary recurrence output is exactly the
`(n−2)`-th mathlib base-3 digit of `√2` itself: `gu(2n) − 3·gu(2n−2) = Real.digits √2 3 (n−2)`. -/
theorem cor12_ternary_sqrt2_literal (n : ℕ) (hn : 2 ≤ n) :
    gu 3 ((9 - 3 * Real.sqrt 2) / 14) (6 + 2 * Real.sqrt 2) 0 (2 * n)
        - 3 * gu 3 ((9 - 3 * Real.sqrt 2) / 14) (6 + 2 * Real.sqrt 2) 0 (2 * n - 2)
      = ((Real.digits (Real.sqrt 2) 3 (n - 2) : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [cor12_ternary_sqrt2 n (by omega)]
  exact digit_recon 3 (Real.sqrt 2) (Real.sqrt_nonneg 2) n hn

end Erdos482.General
