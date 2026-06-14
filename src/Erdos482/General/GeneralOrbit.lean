import Erdos482.General.GeneralDefect

/-!
# The general degree-`d` floor errors as functions of the doubling-orbit coordinates

**Context (the general-`d` analytic bridge).**  `GeneralDefect.lean` reduces the `d`-step impossibility
to the partial defect `g = ∑_{k<d-1} α^{d-1-k} fₖ` of the floor errors `fₖ` at the integer start
`u = ⌊W·2ⁿ⌋`.  To run the equidistribution argument we must express each `fₖ` as a function of the
`Tᵈ` doubling-orbit coordinates `rᵢ = {αⁱ·W·2ⁿ}`.

**This file proves that orbit-coordinate form uniformly for every `k`** (`dStepF_orbit`), the
degree-agnostic analogue of `cubic_f1_orbit`/`cubic_f2_orbit`.  The clean route is the affine-recurrence
closed form (`affine_rec_closed`): since
`α(vₖ + cₖ) = α^{k+1}⌊W2ⁿ⌋ + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ`
and `α^{k+1}⌊W2ⁿ⌋ = ⌊α^{k+1}W2ⁿ⌋ + {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ}`, dropping the integer floor gives
`fₖ = { {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ} + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ }`.
No fresh induction is needed — `affine_rec_closed` already did it.

This is the entry point to the remaining analytic `Tᵈ`-assembly (density + the geometry crux
`exists_partial_defect_outside_window`).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace Erdos482.General

open Finset

/-- **The `k`-th floor error along the doubling orbit, as a function of the orbit coordinates.**
At the integer start `u = ⌊W·2ⁿ⌋`,
`fₖ = { {α^{k+1}W2ⁿ} − α^{k+1}{W2ⁿ} + ∑_{j<k} α^{k-j}(αcⱼ − fⱼ) + αcₖ }`,
where `{W2ⁿ}` and `{α^{k+1}W2ⁿ}` are doubling-orbit fractional coordinates.  Degree-agnostic analogue of
`cubic_f1_orbit` / `cubic_f2_orbit`. -/
theorem dStepF_orbit (α : ℝ) (c : ℕ → ℝ) (W : ℝ) (n k : ℕ) :
    dStepF α c (⌊W * 2 ^ n⌋) k
      = Int.fract (Int.fract (α ^ (k + 1) * (W * 2 ^ n)) - α ^ (k + 1) * Int.fract (W * 2 ^ n)
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c (⌊W * 2 ^ n⌋) j))
          + α * c k) := by
  set u : ℤ := ⌊W * 2 ^ n⌋ with hu
  have hclosed := affine_rec_closed α (dStepV α c u) (fun j => α * c j - dStepF α c u j)
    (dStepV_succ α c u) k
  have harg : α * (dStepV α c u k + c k)
      = (Int.fract (α ^ (k + 1) * (W * 2 ^ n)) - α ^ (k + 1) * Int.fract (W * 2 ^ n)
          + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c u j)) + α * c k)
        + ((⌊α ^ (k + 1) * (W * 2 ^ n)⌋ : ℤ) : ℝ) := by
    have hv0 : dStepV α c u 0 = (u : ℝ) := by rw [dStepV]
    have huf : (u : ℝ) = W * 2 ^ n - Int.fract (W * 2 ^ n) := by
      rw [hu]; exact (Int.self_sub_fract _).symm
    have hflr : Int.fract (α ^ (k + 1) * (W * 2 ^ n)) + ((⌊α ^ (k + 1) * (W * 2 ^ n)⌋ : ℤ) : ℝ)
        = α ^ (k + 1) * (W * 2 ^ n) := Int.fract_add_floor _
    have hsum : α * (∑ j ∈ Finset.range k, α ^ (k - 1 - j) * (α * c j - dStepF α c u j))
        = ∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c u j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ]; ring
    rw [hclosed, hv0, huf]
    linear_combination hsum - hflr
  rw [dStepF, harg, Int.fract_add_intCast]

end Erdos482.General
