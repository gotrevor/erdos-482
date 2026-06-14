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

/-- **The floor errors as an explicit recursion in the orbit-coordinate vector `r`.**  `orbitF α c r k`
builds the `k`-th error purely from `r` (where `r i = {αⁱ·W2ⁿ}`) and the earlier errors, matching
`dStepF_orbit`.  Defined by strong recursion (the body references `orbitF … j` for `j < k`). -/
noncomputable def orbitF (α : ℝ) (c r : ℕ → ℝ) (k : ℕ) : ℝ :=
  Nat.strongRecOn k (fun k IH =>
    Int.fract (r (k + 1) - α ^ (k + 1) * r 0
      + (∑ j ∈ (Finset.range k).attach,
          α ^ (k - j.1) * (α * c j.1 - IH j.1 (Finset.mem_range.mp j.2))) + α * c k))

/-- The defining unfolding of `orbitF` (with the plain `Finset.range` sum). -/
theorem orbitF_eq (α : ℝ) (c r : ℕ → ℝ) (k : ℕ) :
    orbitF α c r k = Int.fract (r (k + 1) - α ^ (k + 1) * r 0
      + (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - orbitF α c r j)) + α * c k) := by
  rw [orbitF, Nat.strongRecOn_eq,
    ← Finset.sum_attach (Finset.range k) (fun j => α ^ (k - j) * (α * c j - orbitF α c r j))]
  rfl

/-- **The floor error along the orbit IS `orbitF` at the canonical coordinate vector** `r i = {αⁱW2ⁿ}`.
Proved by strong induction via `dStepF_orbit` + `orbitF_eq`. -/
theorem dStepF_eq_orbitF (α : ℝ) (c : ℕ → ℝ) (W : ℝ) (n k : ℕ) :
    dStepF α c (⌊W * 2 ^ n⌋) k
      = orbitF α c (fun i => Int.fract (α ^ i * (W * 2 ^ n))) k := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rw [dStepF_orbit, orbitF_eq]
    have hsum : (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - dStepF α c (⌊W * 2 ^ n⌋) j))
        = ∑ j ∈ Finset.range k,
            α ^ (k - j) * (α * c j - orbitF α c (fun i => Int.fract (α ^ i * (W * 2 ^ n))) j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [IH j (Finset.mem_range.mp hj)]
    rw [hsum]
    simp only [pow_zero, one_mul]

/-- The partial defect as an explicit function `dGpd` of the orbit-coordinate vector `r`. -/
noncomputable def dGpd (α : ℝ) (c r : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ k ∈ Finset.range e, α ^ (e - k) * orbitF α c r k

/-- **The partial defect along the base-2 orbit IS `dGpd` at the canonical orbit coordinates**
`r i = {αⁱ·W2ⁿ}` — the degree-agnostic analogue of `cubicPartialDefect_eq_Gpd`.  This expresses the
defect as an explicit function of the `Tᵈ`-orbit point, the object the equidistribution argument
needs. -/
theorem dStepPartial_eq_dGpd (α : ℝ) (c : ℕ → ℝ) (W : ℝ) (n e : ℕ) :
    dStepPartial α c (⌊W * 2 ^ n⌋) (e + 1)
      = dGpd α c (fun i => Int.fract (α ^ i * (W * 2 ^ n))) e := by
  rw [dStepPartial_eq_sum, dGpd]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [dStepF_eq_orbitF]

end Erdos482.General
