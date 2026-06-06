import Erdos482.General.Thm12CaseI

/-!
# Stoll [St05] Corollary 1.1 (Case II specialization) — binary digits of √2

Instantiating the Case-II binary family `thm12_caseII_digits` at `w = √2` (so the mantissa is
`t = √2`, since `1 ≤ √2 < 2`).  Here `√2/(√2+2) = √2 − 1`, so Stoll's coefficient simplifies to
`a = 2j − (√2 − 1) = (2j+1) − √2`, with `b = 2/a`.  For every family parameter `j ≥ 1` this binary
recurrence reads off the base-2 digits of `√2`.  (This is the Case-II slice of Cor 1.1's two
√2-families; `j = 1` gives `a = 3 − √2`.)

Axiom-clean (inherits `thm12_caseII_digits`).
-/

namespace Erdos482.General

open Real

/-- **St05 Cor 1.1 (Case II slice).**  For `j ≥ 1`, `a = (2j+1) − √2`, `b = 2/a`, the recurrence
`gv a b ½` extracts the binary digits of `√2`: for `n ≥ 1`,
`gv(2n) − 2·gv(2n−2) = Real.digits (√2·2^{n−1}/2) 2 0`. -/
theorem cor11_binary_sqrt2 (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 1 ≤ n) :
    gv (2 * (j : ℝ) + 1 - Real.sqrt 2) (2 / (2 * (j : ℝ) + 1 - Real.sqrt 2)) (1 / 2) (2 * n)
        - 2 * gv (2 * (j : ℝ) + 1 - Real.sqrt 2)
            (2 / (2 * (j : ℝ) + 1 - Real.sqrt 2)) (1 / 2) (2 * n - 2)
      = ((Real.digits (Real.sqrt 2 * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := le_of_lt ((Real.lt_sqrt (by norm_num)).mpr (by norm_num))
  have hs2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  -- a = 2j + 1 − √2 equals the Case-II coefficient 2j − √2/(√2+2)
  have ha : 2 * (j : ℝ) + 1 - Real.sqrt 2 = 2 * (j : ℝ) - Real.sqrt 2 / (Real.sqrt 2 + 2) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 + 2 := by positivity
    field_simp
    nlinarith [h2]
  exact thm12_caseII_digits (Real.sqrt 2) hs1 hs2 j hj _ _ ha rfl n hn

/-- **St05 Cor 1.1 (Case I slice).**  The companion √2-family via Case I (`ε = ½`): for `j ≥ 1`,
`a = 2(j−1) + √2` (since `2/(√2+2) = 2 − √2`), `b = 2/a`, the recurrence `gv a b ½` extracts the
binary digits of `√2`.  `j = 1` gives `a = √2 = b` (Graham–Pollak).  Together with
`cor11_binary_sqrt2` (the Case II slice) this is the full Cor 1.1 pair of √2-families. -/
theorem cor11_binary_sqrt2_caseI (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 1 ≤ n) :
    gv (2 * ((j : ℝ) - 1) + Real.sqrt 2) (2 / (2 * ((j : ℝ) - 1) + Real.sqrt 2)) (1 / 2) (2 * n)
        - 2 * gv (2 * ((j : ℝ) - 1) + Real.sqrt 2)
            (2 / (2 * ((j : ℝ) - 1) + Real.sqrt 2)) (1 / 2) (2 * n - 2)
      = ((Real.digits (Real.sqrt 2 * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := le_of_lt ((Real.lt_sqrt (by norm_num)).mpr (by norm_num))
  have hs2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  -- a = 2(j−1) + √2 equals the Case-I coefficient 2j − 2/(√2+2)
  have ha : 2 * ((j : ℝ) - 1) + Real.sqrt 2 = 2 * (j : ℝ) - 2 / (Real.sqrt 2 + 2) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 + 2 := by positivity
    field_simp
    nlinarith [h2]
  exact thm12_caseI_digits (Real.sqrt 2) hs1 hs2 j hj (1 / 2) _ _ (by norm_num) (by norm_num)
    ha rfl n hn

end Erdos482.General
