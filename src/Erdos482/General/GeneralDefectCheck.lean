import Erdos482.General.GeneralDefect
import Erdos482.General.CubicDefect

/-!
# Faithfulness: the cubic engine is the `d = 3` instance of the general one

The general degree-`d` defect engine (`GeneralDefect.lean`) is meant to subsume the hand-rolled,
independently-verified cubic engine (`CubicDefect.lean`).  This file machine-checks that subsumption on
the *map* level: the explicit three-fold-nested floor `cubicV3` is literally `dStepV … 3` for the
schedule `(c₀,c₁,c₂)`, and consequently the abstract `dStep_defect_identity` instantiates to the
already-proven cubic identity `cubicV3_sub_eq`.  This is a genuine cross-check (not a re-proof): it
validates that the general statement is the correct generalization of the verified special case.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace Erdos482.General

/-- The schedule `ℕ → ℝ` extending the cubic offsets `(c₀,c₁,c₂)`. -/
private def cubicSched (c0 c1 c2 : ℝ) : ℕ → ℝ := fun k => if k = 0 then c0 else if k = 1 then c1 else c2

/-- **The cubic three-step map is the `d = 3` instance of the general `dStepV`.** -/
theorem cubicV3_eq_dStepV (α c0 c1 c2 : ℝ) (u : ℤ) :
    ((cubicV3 α c0 c1 c2 u : ℤ) : ℝ) = dStepV α (cubicSched c0 c1 c2) u 3 := by
  simp only [cubicV3, dStepV, cubicSched]
  norm_num

end Erdos482.General
