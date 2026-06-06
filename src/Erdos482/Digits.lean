import Erdos482.Basic

namespace Erdos482
open Real

/-! ## Bridge to mathlib's canonical `Real.digits`

`Real.digits y b i = Fin.ofNat _ ⌊y · b^(i+1)⌋₊` (the base-`b` digits of `y ∈ [0,1)`).
For `x` with `1 ≤ x < 2` (so `Int.fract x = x − 1`), the `i`-th base-2 digit of `Int.fract x`
equals Stoll's floor-difference digit `⌊x·2^(i+1)⌋ − 2·⌊x·2^i⌋`.  This certifies that our
`binDigit` is the standard binary-digit notion. -/

/-- The general digit bridge: `Real.digits (Int.fract x) 2 i` (the `i`-th binary digit of the
fractional part) equals `⌊x·2^(i+1)⌋ − 2·⌊x·2^i⌋`. -/
theorem digit_bridge (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x < 2) (i : ℕ) :
    ((Real.digits (Int.fract x) 2 i : ℕ) : ℤ)
      = ⌊x * 2 ^ (i + 1)⌋ - 2 * ⌊x * 2 ^ i⌋ := by
  have hfloor : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨by exact_mod_cast hx1, by push_cast; linarith⟩
  have hfr : Int.fract x = x - 1 := by
    rw [← Int.self_sub_floor, hfloor]; push_cast; ring
  set N : ℤ := ⌊x * 2 ^ (i + 1)⌋ with hN
  set M : ℤ := ⌊x * 2 ^ i⌋ with hM
  have hz : x * 2 ^ (i + 1) = 2 * (x * 2 ^ i) := by ring
  have hy := Int.floor_le (x * 2 ^ i)
  have hy' := Int.lt_floor_add_one (x * 2 ^ i)
  have hNlb : 2 * M ≤ N := by
    rw [hN, hz, Int.le_floor]; push_cast; linarith
  have hNub : N ≤ 2 * M + 1 := by
    have h : ⌊2 * (x * 2 ^ i)⌋ < 2 * M + 2 := by
      rw [Int.floor_lt]; push_cast; linarith
    rw [hN, hz]; omega
  -- digit side as a Nat mod
  have hdval : ((Real.digits (Int.fract x) 2 i : ℕ) : ℤ)
      = ((⌊Int.fract x * 2 ^ (i + 1)⌋₊ % 2 : ℕ) : ℤ) := by
    simp only [Real.digits, Fin.val_ofNat, Nat.cast_ofNat]
  have hpos : (0:ℝ) ≤ Int.fract x * 2 ^ (i + 1) := by
    rw [hfr]; have : (0:ℝ) ≤ x - 1 := by linarith
    positivity
  have hfn : (⌊Int.fract x * 2 ^ (i + 1)⌋₊ : ℤ) = N - 2 ^ (i + 1) := by
    rw [Int.natCast_floor_eq_floor hpos, hfr,
      show (x - 1) * 2 ^ (i + 1) = x * 2 ^ (i + 1) - ((2 ^ (i + 1) : ℤ) : ℝ) by push_cast; ring,
      Int.floor_sub_intCast]
  have hpow : (2:ℤ) ^ (i + 1) = 2 * 2 ^ i := by ring
  rw [hdval]
  omega

/-- Floor doubling: `⌊2z⌋ − 2⌊z⌋ ∈ {0,1}`. -/
theorem floor_two_mul_sub (z : ℝ) :
    ⌊2 * z⌋ - 2 * ⌊z⌋ = 0 ∨ ⌊2 * z⌋ - 2 * ⌊z⌋ = 1 := by
  have hlb : 2 * ⌊z⌋ ≤ ⌊2 * z⌋ := by
    rw [Int.le_floor]; push_cast; linarith [Int.floor_le z]
  have hub : ⌊2 * z⌋ < 2 * ⌊z⌋ + 2 := by
    rw [Int.floor_lt]; push_cast; linarith [Int.lt_floor_add_one z]
  omega

/-- `binDigit x n` is a genuine bit: it is `0` or `1` (for `n ≥ 1`). -/
theorem binDigit_mem_zero_one (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    binDigit x n = 0 ∨ binDigit x n = 1 := by
  unfold binDigit
  have hpow : (2:ℝ) * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn]
  rw [show x * 2 ^ n = 2 * (x * 2 ^ (n - 1)) by rw [← hpow]; ring]
  exact floor_two_mul_sub (x * 2 ^ (n - 1))

end Erdos482
