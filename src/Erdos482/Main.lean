import Erdos482.Basic
import Erdos482.Induction
import Erdos482.Digits

namespace Erdos482
open Real

/-- **HEADLINE (Graham–Pollak, Erdős #482).**  For the sequence `u 0 = 1`,
`u (n+1) = ⌊√2·(u n + 1/2)⌋`, the quantity `u(2n+1) − 2·u(2n−1)` equals the `n`-th binary digit of
`√2` (in Stoll's floor-formula sense `binDigit`).  Verified numerically: the digits read
`0,1,1,0,1,…` matching `√2 = 1.0110101…₂`. -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := (gp_pair (m + 1)).1
  have h2 := (gp_pair m).1
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [e2, h1, h2]
  unfold binDigit
  rw [Nat.add_sub_cancel]
  ring

/-- **Canonical form.**  `u(2n+1) − 2·u(2n−1)` is literally the `(n−1)`-th base-2 digit of the
fractional part of `√2` under mathlib's `Real.digits` (equivalently, the `n`-th binary digit of
`√2` after the point). -/
theorem graham_pollak_digits (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ)
      = ((Real.digits (Int.fract (Real.sqrt 2)) 2 (n - 1) : ℕ) : ℤ) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have h2 : Real.sqrt 2 < 2 := by nlinarith [hs2, hsnn]
  rw [graham_pollak n hn, digit_bridge (Real.sqrt 2) h1 h2 (n - 1)]
  unfold binDigit
  rw [Nat.sub_add_cancel hn]

/-- **Faithfulness certificate.**  The first three Graham–Pollak digits are `0, 1, 1`, matching the
binary expansion `√2 = 1.0110101…₂`.  Anchors the whole edifice to concrete numbers. -/
theorem binDigit_sqrt2_first_three :
    binDigit (Real.sqrt 2) 1 = 0 ∧ binDigit (Real.sqrt 2) 2 = 1 ∧
      binDigit (Real.sqrt 2) 3 = 1 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have lo : (1.41:ℝ) < Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hi : Real.sqrt 2 < 1.42 := by nlinarith [hs2, hsnn]
  have f0 : ⌊Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f1 : ⌊Real.sqrt 2 * 2⌋ = 2 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f2 : ⌊Real.sqrt 2 * 4⌋ = 5 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  have f3 : ⌊Real.sqrt 2 * 8⌋ = 11 := by
    rw [Int.floor_eq_iff]; constructor <;> · push_cast; nlinarith [lo, hi]
  refine ⟨?_, ?_, ?_⟩ <;> unfold binDigit <;> norm_num [f0, f1, f2, f3]

end Erdos482
