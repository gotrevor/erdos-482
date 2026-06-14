import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Weyl bricks for a.e. equidistribution of the doubling orbit `{2ⁿs}`

`PENDING_WORK.md ★★` reduces the a.e.-`W` cubic impossibility to **a.e. equidistribution of the doubling
orbit `{2ⁿ s}`** (`s ∈ ℝ`), provable WITHOUT a pointwise Birkhoff theorem via the **Davenport–Erdős–
LeVeque** L² method: bound the mean square of the Weyl exponential sum, then apply Borel–Cantelli (both
ingredients are in mathlib).  This file holds the first concrete bricks.

* `char_int`: character orthogonality on `[0,1]`, `∫₀¹ e^{2πi M s} ds = δ_{M,0}`.
* `two_pow_inj`: `(2:ℤ)ⁿ = 2ᵐ ↔ n = m` (used to identify the diagonal of the Weyl double sum).
* `weyl_double_sum_integral`: termwise integration of an abstract double exponential sum.
* `doubling_weyl_L2_mean`: **the Weyl L² mean** `∫₀¹ (∑_{n,m<N} e^{2πi·k·(2ⁿ−2ᵐ)·s}) ds = N` for `k≠0`
  — the mean square of the doubling exponential sum, with only the `N` diagonal terms surviving.

With the L² mean, DEL gives `(1/N)Σ_{n<N} e^{2πi k 2ⁿ s} → 0` a.e. (Borel–Cantelli along `N_j=j²` +
monotonicity), i.e. a.e. base-2 equidistribution — the remaining input for the cubic frontier's path #2.

*Elaboration note.*  Commuting the *double* finite sum through the interval integral whnf-loops if the
summand carries inline integer arithmetic in its cast; `weyl_double_sum_integral` is stated over an
**abstract** `G : ℕ → ℕ → ℤ` precisely so defeq never unfolds that arithmetic; the doubling instance
then follows by `rw [weyl_double_sum_integral …]` and a diagonal count.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section
namespace Erdos482.General

/-- **Character orthogonality on `[0,1]`.**  `∫₀¹ e^{2πi M s} ds = 1` if `M = 0` and `0` otherwise.
The atomic input to the Weyl mean-square estimate for the doubling exponential sum. -/
theorem char_int (M : ℤ) :
    (∫ s in (0:ℝ)..1, Complex.exp (2 * ↑Real.pi * Complex.I * (M:ℂ) * s)) = if M = 0 then 1 else 0 := by
  by_cases hM : M = 0
  · subst hM; simp
  · rw [if_neg hM]
    have hc : (2 * ↑Real.pi * Complex.I * (M:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero, hM]
    have e1 : Complex.exp (2 * ↑Real.pi * Complex.I * (M:ℂ)) = 1 := by
      rw [show (2 * ↑Real.pi * Complex.I * (M:ℂ)) = (M:ℂ) * (2 * ↑Real.pi * Complex.I) from by ring]
      exact Complex.exp_int_mul_two_pi_mul_I M
    rw [integral_exp_mul_complex hc]; simp [e1]

/-- `(2:ℤ)ⁿ = 2ᵐ ↔ n = m`: the doubling powers are distinct, so `k·(2ⁿ−2ᵐ) = 0` (for `k ≠ 0`) exactly
on the diagonal `n = m` — the terms that survive in the Weyl mean square. -/
theorem two_pow_inj (n m : ℕ) : ((2:ℤ)^n = 2^m) ↔ n = m := by
  constructor
  · intro h
    have : (2:ℕ)^n = 2^m := by exact_mod_cast h
    exact Nat.pow_right_injective (le_refl 2) this
  · rintro rfl; rfl

/-- Termwise integration of an abstract double exponential sum.  Stated over an **abstract**
`G : ℕ → ℕ → ℤ` so that `defeq` never unfolds inline integer arithmetic in the cast (which otherwise
makes the integral/double-sum commute whnf-loop).  Each term integrates by `char_int`. -/
theorem weyl_double_sum_integral (G : ℕ → ℕ → ℤ) (N : ℕ) :
    (∫ s in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((G n m : ℤ):ℂ) * s))
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if G n m = 0 then (1:ℂ) else 0) := by
  have hcont : ∀ (n m : ℕ), Continuous (fun s : ℝ =>
      Complex.exp (2 * ↑Real.pi * Complex.I * ((G n m :ℤ):ℂ) * s)) := fun n m =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [intervalIntegral.integral_finset_sum (fun n _ =>
      (continuous_finset_sum (Finset.range N) (fun m _ => hcont n m)).intervalIntegrable 0 1)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [intervalIntegral.integral_finset_sum (fun m _ => (hcont n m).intervalIntegrable 0 1)]
  exact Finset.sum_congr rfl (fun m _ => char_int (G n m))

/-- **Weyl L² mean of the doubling exponential sum.**  For `k ≠ 0`,
`∫₀¹ (∑_{n,m<N} e^{2πi·k·(2ⁿ−2ᵐ)·s}) ds = N` — the mean square `∫₀¹ |∑_{n<N} e^{2πi·k·2ⁿ·s}|² ds`
written out.  The characters are L²-orthogonal (`char_int`), so only the `N` diagonal terms `n=m`
(`two_pow_inj`, as `k≠0`) survive.  This is the mean-square bound that feeds Davenport–Erdős–LeVeque to
yield a.e. base-2 equidistribution of `{2ⁿs}` (`PENDING_WORK.md ★★`). -/
theorem doubling_weyl_L2_mean (k : ℤ) (hk : k ≠ 0) (N : ℕ) :
    (∫ s in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        Complex.exp (2 * ↑Real.pi * Complex.I * ((k * ((2:ℤ)^n - 2^m) : ℤ):ℂ) * s)) = (N:ℂ) := by
  rw [weyl_double_sum_integral (fun n m => k * ((2:ℤ)^n - 2^m)) N]
  have cond : ∀ n m : ℕ, (k * ((2:ℤ)^n - 2^m) = 0) ↔ (m = n) := by
    intro n m; rw [mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hk
      · exact ((two_pow_inj n m).mp h).symm
    · rintro rfl; right; rfl
  calc ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if k * ((2:ℤ)^n - 2^m) = 0 then (1:ℂ) else 0)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if m = n then (1:ℂ) else 0) :=
        Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => if_congr (cond n m) rfl rfl))
    _ = ∑ n ∈ Finset.range N, (1:ℂ) :=
        Finset.sum_congr rfl (fun n hn => by
          rw [Finset.sum_ite_eq' (Finset.range N) n (fun _ => (1:ℂ)), if_pos hn])
    _ = (N:ℂ) := by simp [Finset.sum_const, Finset.card_range]

end Erdos482.General
