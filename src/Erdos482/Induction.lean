import Erdos482.Basic
import Erdos482.Crux

namespace Erdos482
open Real

/-! ## The two Graham–Pollak floor identities, corrected to faithful index form

Stoll §4 specialized to GP (verified numerically against the sequence):
* (6')  `u (2j+1) = ⌊√2·2^j⌋ + 2^j`
* (5')  `u (2j+2) = ⌊√2·2^j⌋ + 2^(j+1)`

The even→odd step is exactly `crux`; the odd→even step is the eq-(8) interval check below.
-/

/-- Stoll eq (8) interval check (GP, ε = 1/2): for `w ∈ [0,1)`,
`0 ≤ w·(1−√2) + √2/2 < 1`.  Used by the odd→even induction step. -/
private lemma eq8 {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) :
    0 ≤ w * (1 - Real.sqrt 2) + Real.sqrt 2 / 2 ∧
      w * (1 - Real.sqrt 2) + Real.sqrt 2 / 2 < 1 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - w) (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)]
  · nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ Real.sqrt 2 - 1)]

/-- even→odd floor step: from `u(2j+2) = ⌊√2·2^j⌋ + 2^(j+1)` derive `u(2j+3) = ⌊√2·2^(j+1)⌋ + 2^(j+1)`.
Reduces to `crux (√2·2^(j+1))`. -/
private lemma floorB (j : ℕ) :
    ⌊Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨cl, cu⟩ := crux (Real.sqrt 2 * 2 ^ (j + 1))
  have hhalf : Real.sqrt 2 * 2 ^ (j + 1) / 2 = Real.sqrt 2 * 2 ^ j := by ring
  rw [hhalf] at cl cu
  have key : Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)
      = ((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ)
        + (Int.fract (Real.sqrt 2 * 2 ^ (j + 1))
            - Real.sqrt 2 * Int.fract (Real.sqrt 2 * 2 ^ j) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * 2 ^ (j + 1)), ← Int.self_sub_floor (Real.sqrt 2 * 2 ^ j)]
    push_cast
    linear_combination (2:ℝ) ^ j * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨cl, cu⟩, add_zero]

/-- odd→even floor step: from `u(2j+3) = ⌊√2·2^(j+1)⌋ + 2^(j+1)` derive
`u(2j+4) = ⌊√2·2^(j+1)⌋ + 2^(j+2)`.  Reduces to `eq8`. -/
private lemma floorA (j : ℕ) :
    ⌊Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 2) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨el, eu⟩ := eq8 (Int.fract_nonneg (Real.sqrt 2 * 2 ^ (j + 1)))
    (Int.fract_lt_one (Real.sqrt 2 * 2 ^ (j + 1)))
  have key : Real.sqrt 2 * (((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ) + 1 / 2)
      = ((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 2) : ℤ) : ℝ)
        + (Int.fract (Real.sqrt 2 * 2 ^ (j + 1)) * (1 - Real.sqrt 2) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * 2 ^ (j + 1))]
    push_cast
    linear_combination (2:ℝ) ^ (j + 1) * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨el, eu⟩, add_zero]

/-- The recurrence over ℤ (the argument is nonnegative, so `Nat.floor = Int.floor`). -/
private lemma urec (n : ℕ) :
    (u (n + 1) : ℤ) = ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋ := by
  have h : u (n + 1) = ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊ := rfl
  rw [h, Int.natCast_floor_eq_floor (by positivity)]

/-- The joint Graham–Pollak identities, proved by induction on `j`. -/
theorem gp_pair (j : ℕ) :
    (u (2 * j + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ j ∧
      (u (2 * j + 2) : ℤ) = ⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hs2, sq_nonneg (Real.sqrt 2 - 2)]
  have hlo : (4:ℝ) / 3 ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  induction j with
  | zero =>
    have hfloors : ⌊Real.sqrt 2⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> [exact_mod_cast hs1; · push_cast; linarith]
    have hu1 : (u 1 : ℤ) = 2 := by
      rw [urec 0]
      have : u 0 = 1 := rfl
      rw [this]
      push_cast
      rw [Int.floor_eq_iff]; constructor <;> [(push_cast; nlinarith); (push_cast; nlinarith)]
    have hu2 : (u 2 : ℤ) = 3 := by
      have e : (2:ℕ) = 1 + 1 := rfl
      rw [e, urec 1]
      rw [show ((u 1 : ℝ)) = ((u 1 : ℤ) : ℝ) by push_cast; ring, hu1]
      push_cast
      rw [Int.floor_eq_iff]; constructor <;> [(push_cast; nlinarith); (push_cast; nlinarith)]
    refine ⟨?_, ?_⟩
    · simpa [hfloors] using hu1
    · simpa [hfloors] using hu2
  | succ j IH =>
    have h2r : ((u (2 * j + 2) : ℕ) : ℝ)
        = ((⌊Real.sqrt 2 * 2 ^ j⌋ + 2 ^ (j + 1) : ℤ) : ℝ) := by exact_mod_cast IH.2
    have step1 : (u (2 * j + 2 + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) := by
      rw [urec (2 * j + 2), h2r]; exact floorB j
    have h3r : ((u (2 * j + 2 + 1) : ℕ) : ℝ)
        = ((⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1) : ℤ) : ℝ) := by exact_mod_cast step1
    have step2 : (u (2 * j + 2 + 1 + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 2) := by
      rw [urec (2 * j + 2 + 1), h3r]; exact floorA j
    refine ⟨?_, ?_⟩
    · show (u (2 * (j + 1) + 1) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1)
      have : 2 * (j + 1) + 1 = 2 * j + 2 + 1 := by ring
      rw [this]; exact step1
    · show (u (2 * (j + 1) + 2) : ℤ) = ⌊Real.sqrt 2 * 2 ^ (j + 1)⌋ + 2 ^ (j + 1 + 1)
      have : 2 * (j + 1) + 2 = 2 * j + 2 + 1 + 1 := by ring
      rw [this]; exact step2

end Erdos482
