import Erdos482.General.St06Thm34
import Erdos482.Induction
import Erdos482.Digits
import Mathlib.NumberTheory.Rayleigh

/-!
# Stoll [St06] Corollary 3.5 — the Beatty foundation

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Corollary 3.5.  The elegant capstone unifies the binary digit-extraction recurrences
via **Beatty's / Rayleigh's theorem**: the two Beatty sequences `B⁺(1+√2)` and `B⁺(1+1/√2)` partition
the positive integers, and (extended to all signs) every `m ∈ ℤ∖{−1,0}` is `⌊r(1+1/√2)⌋` or
`⌊r(1+√2)⌋` for a unique `r`, which fixes the `w` whose binary digits the `√2`-recurrence reproduces.

This module establishes the **verified Beatty foundation** that the full corollary rests on:
* `Erdos482.General.irrational_one_add_sqrt2` — `1 + √2` is irrational;
* `Erdos482.General.holderConjugate_one_add_sqrt2` — `(1+√2)` and `(1+1/√2)` are Hölder conjugate
  (`(1+√2)⁻¹ + (1+1/√2)⁻¹ = 1`), the exact hypothesis Rayleigh's theorem needs;
* `Erdos482.General.beatty_partition_sqrt2` — Rayleigh's partition for this conjugate pair:
  `{⌊k(1+√2)⌋ | k>0} ∆ {⌊k(1+1/√2)⌋ | k>0} = ℤ_{>0}`.

The remaining step of Cor 3.5 — packaging, for each representable `m`, the `w = w(r)` and the index
shift `M = ⌊log₂ w⌋` so that `su √2 √2 (1/2) (1/2) m` reproduces `w`'s digits via the (already proved)
digit theorem — is the next increment (see `notes/ST06-PLAN.md` Cor 3.5; the per-`w` recurrence is the
`m=1,(l,k)=(0,0)` Graham–Pollak instance of `St06Thm33`).  Axiom-clean.
-/

namespace Erdos482.General

open Real
open scoped symmDiff

/-- `1 + √2` is irrational. -/
theorem irrational_one_add_sqrt2 : Irrational (1 + Real.sqrt 2) := by
  simpa using Irrational.intCast_add irrational_sqrt_two 1

/-- **The Beatty parameters of Cor 3.5 are Hölder conjugate.**  `(1+√2)⁻¹ + (1+1/√2)⁻¹ = 1`, so
Rayleigh's theorem applies to the pair `(1+√2, 1+1/√2)`. -/
theorem holderConjugate_one_add_sqrt2 :
    Real.HolderConjugate (1 + Real.sqrt 2) (1 + 1 / Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (1 : ℝ) < 1 + Real.sqrt 2 := by linarith
  rw [Real.holderConjugate_iff]
  refine ⟨h1, ?_⟩
  have hd1 : 1 + Real.sqrt 2 ≠ 0 := by positivity
  have hd2 : 1 + 1 / Real.sqrt 2 ≠ 0 := by positivity
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [h2, hpos]

/-- **Rayleigh's theorem for the Cor 3.5 pair.**  The Beatty sequences of `1+√2` and `1+1/√2`
partition the positive integers:  `B⁺(1+√2) ∆ B⁺(1+1/√2) = ℤ_{>0}`. -/
theorem beatty_partition_sqrt2 :
    {beattySeq (1 + Real.sqrt 2) k | k > 0}
      ∆ {beattySeq (1 + 1 / Real.sqrt 2) k | k > 0} = {n | 0 < n} :=
  irrational_one_add_sqrt2.beattySeq_symmDiff_beattySeq_pos holderConjugate_one_add_sqrt2

/-- **The explicit Cor 3.5 partition.**  Every positive integer is a value of *exactly one* of the
two Beatty sequences `B⁺(1+√2)`, `B⁺(1+1/√2)` — the form Stoll uses to characterise the representable
`m`.  (Extracted from `beatty_partition_sqrt2` via `Set.mem_symmDiff`.) -/
theorem beatty_unique_sqrt2 (n : ℤ) (hn : 0 < n) :
    ((∃ k > 0, beattySeq (1 + Real.sqrt 2) k = n)
        ∧ ¬ ∃ k > 0, beattySeq (1 + 1 / Real.sqrt 2) k = n)
      ∨ (¬ (∃ k > 0, beattySeq (1 + Real.sqrt 2) k = n)
        ∧ ∃ k > 0, beattySeq (1 + 1 / Real.sqrt 2) k = n) := by
  have hmem : n ∈ {beattySeq (1 + Real.sqrt 2) k | k > 0}
      ∆ {beattySeq (1 + 1 / Real.sqrt 2) k | k > 0} := by
    rw [beatty_partition_sqrt2]; exact hn
  rcases Set.mem_symmDiff.mp hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩

/-! ## The Cor 3.5 digit engine — generalized Graham–Pollak (factor `r`)

The Graham–Pollak recurrence `su √2 √2 ½ ½ m` (both steps `⌊√2·(·+½)⌋`) started at the Beatty value
`m = ⌊r·(1+1/√2)⌋ = r + ⌊r√2/2⌋` (case 1) or `m = ⌊r·(1+√2)⌋ = r + ⌊r√2⌋` (case 2) reads off the
binary digits of `r·√2`.  This is the classical `gp_pair` (the `r=1` case) generalized by a free
factor `r ∈ ℕ`; the `s`-cancellation crux (`Erdos482.crux`) and the odd-step bound
(`Erdos482.eq8_general`, at `ε=½`) are both universal, so inserting `r` is mechanical. -/

/-- The Cor 3.5 recurrence step is the uniform Graham–Pollak step (both parities apply `⌊√2(·+½)⌋`). -/
theorem su_gp_succ (m : ℤ) (n : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) m (n + 1)
      = ⌊Real.sqrt 2 * ((su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) m n : ℝ) + 1 / 2)⌋ := by
  rw [su_succ]; split <;> rfl

/-- Base step (`su 0 → su 1`): from the Beatty start `m = r + ⌊√2 r/2⌋` the first step lands on
`⌊√2·r⌋ + r`.  Reduces to `crux (√2·r)`. -/
private lemma cor35_base (r : ℕ) :
    ⌊Real.sqrt 2 * ((((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋ : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨cl, cu⟩ := crux (Real.sqrt 2 * (r : ℝ))
  have key : Real.sqrt 2 * ((((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋ : ℤ) : ℝ) + 1 / 2)
      = (((⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ) : ℤ)) : ℝ)
        + (Int.fract (Real.sqrt 2 * (r : ℝ))
            - Real.sqrt 2 * Int.fract (Real.sqrt 2 * (r : ℝ) / 2) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * (r : ℝ)),
        ← Int.self_sub_floor (Real.sqrt 2 * (r : ℝ) / 2)]
    push_cast
    linear_combination ((r : ℝ) / 2) * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨cl, cu⟩, add_zero]

/-- odd→even floor step (factor `r`): from `⌊√2·r·2^p⌋ + r·2^p` to `⌊√2·r·2^p⌋ + r·2^(p+1)`. -/
private lemma cor35_floorA (r p : ℕ) :
    ⌊Real.sqrt 2 * (((⌊Real.sqrt 2 * (r : ℝ) * 2 ^ p⌋ + (r : ℤ) * 2 ^ p : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ p⌋ + (r : ℤ) * 2 ^ (p + 1) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hs1' : (1 : ℝ) < Real.sqrt 2 := by nlinarith [hs2, hsnn]
  obtain ⟨el, eu⟩ := eq8_general (ε := 1 / 2) (by linarith) (by linarith)
    (Int.fract_nonneg (Real.sqrt 2 * (r : ℝ) * 2 ^ p))
    (Int.fract_lt_one (Real.sqrt 2 * (r : ℝ) * 2 ^ p))
  have key : Real.sqrt 2 * (((⌊Real.sqrt 2 * (r : ℝ) * 2 ^ p⌋ + (r : ℤ) * 2 ^ p : ℤ) : ℝ) + 1 / 2)
      = ((⌊Real.sqrt 2 * (r : ℝ) * 2 ^ p⌋ + (r : ℤ) * 2 ^ (p + 1) : ℤ) : ℝ)
        + (Int.fract (Real.sqrt 2 * (r : ℝ) * 2 ^ p) * (1 - Real.sqrt 2) + Real.sqrt 2 * (1 / 2)) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * (r : ℝ) * 2 ^ p)]
    push_cast
    linear_combination ((r : ℝ) * 2 ^ p) * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨el, eu⟩, add_zero]

/-- even→odd floor step (factor `r`): from `⌊√2·r·2^p⌋ + r·2^(p+1)` to `⌊√2·r·2^(p+1)⌋ + r·2^(p+1)`. -/
private lemma cor35_floorB (r p : ℕ) :
    ⌊Real.sqrt 2 * (((⌊Real.sqrt 2 * (r : ℝ) * 2 ^ p⌋ + (r : ℤ) * 2 ^ (p + 1) : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (p + 1)⌋ + (r : ℤ) * 2 ^ (p + 1) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨cl, cu⟩ := crux (Real.sqrt 2 * (r : ℝ) * 2 ^ (p + 1))
  have hhalf : Real.sqrt 2 * (r : ℝ) * 2 ^ (p + 1) / 2 = Real.sqrt 2 * (r : ℝ) * 2 ^ p := by ring
  rw [hhalf] at cl cu
  have key : Real.sqrt 2 * (((⌊Real.sqrt 2 * (r : ℝ) * 2 ^ p⌋ + (r : ℤ) * 2 ^ (p + 1) : ℤ) : ℝ) + 1 / 2)
      = ((⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (p + 1)⌋ + (r : ℤ) * 2 ^ (p + 1) : ℤ) : ℝ)
        + (Int.fract (Real.sqrt 2 * (r : ℝ) * 2 ^ (p + 1))
            - Real.sqrt 2 * Int.fract (Real.sqrt 2 * (r : ℝ) * 2 ^ p) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor (Real.sqrt 2 * (r : ℝ) * 2 ^ (p + 1)),
        ← Int.self_sub_floor (Real.sqrt 2 * (r : ℝ) * 2 ^ p)]
    push_cast
    linear_combination ((r : ℝ) * 2 ^ p) * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨cl, cu⟩, add_zero]

/-- **The Cor 3.5 engine, case 1** (`1+1/√2` Beatty branch).  Joint closed forms of the GP recurrence
started at `m = r + ⌊√2 r/2⌋ = ⌊r(1+1/√2)⌋`, by induction. -/
theorem cor35_pair (r j : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * j + 1)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ + (r : ℤ) * 2 ^ j ∧
      su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * j + 2)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ + (r : ℤ) * 2 ^ (j + 1) := by
  induction j with
  | zero =>
    have h1 : su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (0 + 1) = ⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ) := by
      rw [su_gp_succ, su_zero]; exact cor35_base r
    refine ⟨?_, ?_⟩
    · simpa [pow_zero, mul_one] using h1
    · have h2 : su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (0 + 1 + 1)
          = ⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ) * 2 := by
        rw [su_gp_succ, h1]
        have := cor35_floorA r 0
        simpa [pow_zero, mul_one, pow_one] using this
      simpa [pow_zero, mul_one, pow_one] using h2
  | succ j IH =>
    obtain ⟨IH1, IH2⟩ := IH
    have step1 : su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * j + 2 + 1)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (j + 1)⌋ + (r : ℤ) * 2 ^ (j + 1) := by
      rw [su_gp_succ, IH2]; exact_mod_cast cor35_floorB r j
    have step2 : su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * j + 2 + 1 + 1)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (j + 1)⌋ + (r : ℤ) * 2 ^ (j + 2) := by
      rw [su_gp_succ, step1]; exact_mod_cast cor35_floorA r (j + 1)
    refine ⟨?_, ?_⟩
    · show su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * (j + 1) + 1) = _
      rw [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by ring]; exact step1
    · show su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * (j + 1) + 2) = _
      rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 1 + 1 by ring]; exact step2

/-- **The Cor 3.5 engine, case 2** (`1+√2` Beatty branch).  Joint closed forms of the GP recurrence
started at `m = r + ⌊√2 r⌋ = ⌊r(1+√2)⌋`.  (Base case is `cor35_floorA` at `p=0` — no separate crux
base, since the start is already in `A`-form.) -/
theorem cor35_pair_case2 (r j : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * j)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ + (r : ℤ) * 2 ^ j ∧
      su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * j + 1)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ + (r : ℤ) * 2 ^ (j + 1) := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · show su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) 0 = _
      rw [su_zero]; simp [pow_zero, mul_one]
    · show su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (0 + 1) = _
      rw [su_gp_succ, su_zero]
      have := cor35_floorA r 0
      simpa [pow_zero, mul_one, pow_one] using this
  | succ j IH =>
    obtain ⟨IH1, IH2⟩ := IH
    have step1 : su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * j + 1 + 1)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (j + 1)⌋ + (r : ℤ) * 2 ^ (j + 1) := by
      rw [su_gp_succ, IH2]; exact_mod_cast cor35_floorB r j
    have step2 : su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * j + 1 + 1 + 1)
        = ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (j + 1)⌋ + (r : ℤ) * 2 ^ (j + 2) := by
      rw [su_gp_succ, step1]; exact_mod_cast cor35_floorA r (j + 1)
    refine ⟨?_, ?_⟩
    · show su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * (j + 1)) = _
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; exact step1
    · show su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
          (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * (j + 1) + 1) = _
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]; exact step2

/-- Helper: `⌊√2·r·2^(j+1)⌋ − 2⌊√2·r·2^j⌋ = binDigit (r√2) (j+1)`, aligning the floor arguments. -/
private lemma cor35_floorDiff (r j : ℕ) :
    (⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (j + 1)⌋ - 2 * ⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ : ℤ)
      = binDigit ((r : ℝ) * Real.sqrt 2) (j + 1) := by
  have e1 : (⌊Real.sqrt 2 * (r : ℝ) * 2 ^ (j + 1)⌋ : ℤ) = ⌊(r : ℝ) * Real.sqrt 2 * 2 ^ (j + 1)⌋ := by
    congr 1; ring
  have e2 : (⌊Real.sqrt 2 * (r : ℝ) * 2 ^ j⌋ : ℤ) = ⌊(r : ℝ) * Real.sqrt 2 * 2 ^ ((j + 1) - 1)⌋ := by
    rw [Nat.add_sub_cancel]; congr 1; ring
  rw [binDigit, e1, e2]

/-- **Cor 3.5 digit extraction, case 1.**  Started at the Beatty value `m = ⌊r(1+1/√2)⌋ = r+⌊√2 r/2⌋`,
the Graham–Pollak recurrence reads off the binary digits of `r√2`. -/
theorem cor35_digits_case1 (r j : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * (j + 1) + 1)
      - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        ((r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋) (2 * j + 1)
      = binDigit ((r : ℝ) * Real.sqrt 2) (j + 1) := by
  rw [(cor35_pair r (j + 1)).1, (cor35_pair r j).1, ← cor35_floorDiff]; ring

/-- **Cor 3.5 digit extraction, case 2.**  Started at the Beatty value `m = ⌊r(1+√2)⌋ = r+⌊√2 r⌋`,
the Graham–Pollak recurrence reads off the binary digits of `r√2`. -/
theorem cor35_digits_case2 (r j : ℕ) :
    su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * (j + 1) + 1)
      - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2)
        (⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ)) (2 * j + 1)
      = binDigit ((r : ℝ) * Real.sqrt 2) (j + 1) := by
  rw [(cor35_pair_case2 r (j + 1)).2, (cor35_pair_case2 r j).2, ← cor35_floorDiff]; ring

/-! ## Beatty connection and the capstone -/

/-- The case-1 Beatty value `beattySeq (1+1/√2) r = ⌊r(1+1/√2)⌋` equals the case-1 start
`r + ⌊√2 r/2⌋`. -/
private lemma beatty_start_case1 (r : ℕ) :
    beattySeq (1 + 1 / Real.sqrt 2) (r : ℤ) = (r : ℤ) + ⌊Real.sqrt 2 * (r : ℝ) / 2⌋ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hhalf : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hpos
    field_simp
    linarith [h2]
  have key : ((r : ℤ) : ℝ) * (1 + 1 / Real.sqrt 2) = ((r : ℤ) : ℝ) + Real.sqrt 2 * (r : ℝ) / 2 := by
    rw [hhalf]; push_cast; ring
  simp only [beattySeq]
  rw [key, Int.floor_intCast_add]

/-- The case-2 Beatty value `beattySeq (1+√2) r = ⌊r(1+√2)⌋` equals the case-2 start `⌊√2 r⌋ + r`. -/
private lemma beatty_start_case2 (r : ℕ) :
    beattySeq (1 + Real.sqrt 2) (r : ℤ) = ⌊Real.sqrt 2 * (r : ℝ)⌋ + (r : ℤ) := by
  have key : ((r : ℤ) : ℝ) * (1 + Real.sqrt 2) = ((r : ℤ) : ℝ) + Real.sqrt 2 * (r : ℝ) := by
    push_cast; ring
  simp only [beattySeq]
  rw [key, Int.floor_intCast_add, add_comm]

/-- **Stoll [St06] Corollary 3.5 — the Beatty unification (capstone).**  For every positive integer
`n`, the Graham–Pollak recurrence `su √2 √2 ½ ½ n` (start `n`) reads off the binary digits of `r·√2`
for a unique `r ≥ 1` determined by which Beatty sequence (`1+√2` or `1+1/√2`) contains `n`
(`beatty_unique_sqrt2`).  This unifies the Borwein–Bailey digit-extraction examples: every admissible
start corresponds, via Rayleigh's partition, to exactly one multiple `r√2`. -/
theorem st06_cor35 (n : ℤ) (hn : 0 < n) :
    ∃ r : ℕ, 0 < r ∧ ∀ j : ℕ,
      su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * (j + 1) + 1)
        - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * j + 1)
      = binDigit ((r : ℝ) * Real.sqrt 2) (j + 1) := by
  rcases beatty_unique_sqrt2 n hn with ⟨⟨k, hk, hkn⟩, _⟩ | ⟨_, ⟨k, hk, hkn⟩⟩
  · -- `n ∈ B(1+√2)` (case 2)
    refine ⟨k.toNat, by omega, fun j => ?_⟩
    have hkr : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
    have hn' : n = ⌊Real.sqrt 2 * (k.toNat : ℝ)⌋ + (k.toNat : ℤ) := by
      rw [← beatty_start_case2 k.toNat, hkr, hkn]
    rw [hn']; exact cor35_digits_case2 k.toNat j
  · -- `n ∈ B(1+1/√2)` (case 1)
    refine ⟨k.toNat, by omega, fun j => ?_⟩
    have hkr : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
    have hn' : n = (k.toNat : ℤ) + ⌊Real.sqrt 2 * (k.toNat : ℝ) / 2⌋ := by
      rw [← beatty_start_case1 k.toNat, hkr, hkn]
    rw [hn']; exact cor35_digits_case1 k.toNat j

/-- `binDigit x (j+1) = Real.digits x 2 j` — the Graham–Pollak difference convention coincides with
mathlib's `Real.digits` (a pure floor identity for `x ≥ 0`). -/
private lemma binDigit_succ_eq_realDigits (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    binDigit x (j + 1) = ((Real.digits x 2 j : ℕ) : ℤ) := by
  rw [binDigit, Nat.add_sub_cancel, digits_eq_floor_sub x hx]

/-- **Cor 3.5, literal form.**  The Graham–Pollak difference of the recurrence started at `n` is the
genuine mathlib binary digit `Real.digits (r√2) 2 j` of `r·√2`, for the Beatty-determined `r`. -/
theorem st06_cor35_realDigits (n : ℤ) (hn : 0 < n) :
    ∃ r : ℕ, 0 < r ∧ ∀ j : ℕ,
      su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * (j + 1) + 1)
        - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * j + 1)
      = ((Real.digits ((r : ℝ) * Real.sqrt 2) 2 j : ℕ) : ℤ) := by
  obtain ⟨r, hr, hdig⟩ := st06_cor35 n hn
  exact ⟨r, hr, fun j => by rw [hdig j, binDigit_succ_eq_realDigits _ (by positivity)]⟩

/-- **Cor 3.5, bit form.**  The Graham–Pollak difference is a genuine binary digit (`0` or `1`). -/
theorem st06_cor35_isBit (n : ℤ) (hn : 0 < n) :
    ∃ r : ℕ, 0 < r ∧ ∀ j : ℕ,
      su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * (j + 1) + 1)
          - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * j + 1) = 0 ∨
      su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * (j + 1) + 1)
          - 2 * su (Real.sqrt 2) (Real.sqrt 2) (1 / 2) (1 / 2) n (2 * j + 1) = 1 := by
  obtain ⟨r, hr, hdig⟩ := st06_cor35 n hn
  exact ⟨r, hr, fun j => by rw [hdig j]; exact binDigit_mem_zero_one _ (j + 1) (by omega)⟩

end Erdos482.General
