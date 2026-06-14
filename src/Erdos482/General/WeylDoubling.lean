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

**Next brick (target, math fully worked out — see `PENDING_WORK.md`).** The Weyl L² mean
`∫₀¹ (∑_{n,m<N} e^{2πi·k·(2ⁿ−2ᵐ)·s}) ds = N` for `k ≠ 0`: expand `|∑_{n<N} e^{2πi k 2ⁿ s}|²`, integrate
termwise (`char_int`), only the `N` diagonal terms (`two_pow_inj`) survive.  The statement elaborates;
the only obstacle is an elaboration-performance wall when commuting the *double* finite sum through the
interval integral (`intervalIntegral.integral_finset_sum` whnf-loops on the explicit summand) — finish
by first collapsing to a single sum over `Finset.range N ×ˢ Finset.range N` via `Finset.sum_product'`,
or hand to Aristotle.  With the L² mean, DEL gives `(1/N)Σ_{n<N} e^{2πi k 2ⁿ s} → 0` a.e., i.e. a.e.
base-2 equidistribution — the remaining input for the cubic frontier's path #2.
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

end Erdos482.General
