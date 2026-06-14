import Erdos482.General.GeneralOrbit
import Erdos482.General.GeneralTorusEquidist
import Erdos482.General.CubicFinish
import Erdos482.General.RpowWindow

/-!
# Torus-level plumbing for the general degree-`d` finish

Expresses the partial defect `dStepPartial` along the base-2 orbit as a function `dGpdTorus` on the
torus `Tᵈ = (ℝ/ℤ)ᵈ` (reusing `CubicFinish.torusRep`, the interior chart `ℝ/ℤ → [0,1)`), and proves it
is `ContinuousAt` torus points with nonzero coordinates and non-integer inner arguments.  This is the
glue between the algebraic engine (`GeneralOrbit.dGpd`) and the geometric input
(`GeneralTorusEquidist.ae_W_dTorus_orbit_dense`); the only remaining step to the general headline is the
nonzero-coordinate realization (see `PENDING_WORK.md`).
-/

open Filter MeasureTheory AddCircle
open scoped Topology

noncomputable section
namespace Erdos482.General

/-- The `ℕ → ℝ` coordinate vector of a torus point (chart representatives, `0` past index `d`). -/
def coordsOf (d : ℕ) (a : Fin d → AddCircle (1 : ℝ)) : ℕ → ℝ :=
  fun i => if h : i < d then torusRep (a ⟨i, h⟩) else 0

/-- The partial-defect function on `Tᵈ`: `dGpd` evaluated at the chart representatives. -/
def dGpdTorus (d : ℕ) (α : ℝ) (c : ℕ → ℝ) (a : Fin d → AddCircle (1 : ℝ)) : ℝ :=
  dGpd α c (coordsOf d a) (d - 1)

/-- **`dGpdTorus` reads the partial defect along the base-2 orbit**: at seed `W`, step `n`,
`dGpdTorus d α c (dTorusOrbit d W n) = dStepPartial α c (⌊W·2ⁿ⌋) d` (`α = 2^{1/d}`).  General analogue
of `cubicGpdTorus_orbit`. -/
theorem dGpdTorus_orbit (d : ℕ) (hd : 1 ≤ d) (c : ℕ → ℝ) (W : ℝ) (n : ℕ) :
    dGpdTorus d (rrt d) c (dTorusOrbit d W n) = dStepPartial (rrt d) c (⌊W * 2 ^ n⌋) d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [dGpdTorus, Nat.add_sub_cancel,
    dGpd_congr (rrt (e + 1)) c (coordsOf (e + 1) (dTorusOrbit (e + 1) W n))
      (fun i => Int.fract ((rrt (e + 1)) ^ i * (W * 2 ^ n))) e ?_,
    ← dStepPartial_eq_dGpd]
  intro i hi
  have hid : i < e + 1 := by omega
  simp only [coordsOf, dif_pos hid, dTorusOrbit, torusRep_coe]
  congr 1
  ring

/-- **`dGpdTorus` is `ContinuousAt` any torus point with nonzero coordinates and non-integer inner
arguments** — the general analogue of `continuousAt_cubicGpdTorus`. -/
theorem continuousAt_dGpdTorus (d : ℕ) (α : ℝ) (c : ℕ → ℝ) (P : Fin d → AddCircle (1 : ℝ))
    (hne : ∀ i, P i ≠ 0)
    (harg : ∀ k, k < d - 1 →
      orbitArg α c (coordsOf d P) k ≠ ((⌊orbitArg α c (coordsOf d P) k⌋ : ℤ) : ℝ)) :
    ContinuousAt (dGpdTorus d α c) P := by
  have hcoord : ContinuousAt (fun a : Fin d → AddCircle (1 : ℝ) => coordsOf d a) P := by
    refine continuousAt_pi.2 (fun i => ?_)
    by_cases h : i < d
    · simp only [coordsOf, dif_pos h]
      exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin d → AddCircle (1 : ℝ) => a ⟨i, h⟩)
        (continuousAt_torusRep (hne ⟨i, h⟩)) (continuous_apply (⟨i, h⟩ : Fin d)).continuousAt
    · simp only [coordsOf, dif_neg h]
      exact continuousAt_const
  exact ContinuousAt.comp (g := fun r : ℕ → ℝ => dGpd α c r (d - 1))
    (f := fun a : Fin d → AddCircle (1 : ℝ) => coordsOf d a)
    (continuousAt_dGpd α c (coordsOf d P) (d - 1) harg) hcoord

/-- **The general-`d` impossibility, modulo the geometry crux.**  For `α = 2^{1/d}` (`d ≥ 1`), a fixed
schedule `c`, and *any* torus point `P` with nonzero coordinates and non-integer inner arguments whose
partial-defect value `dGpdTorus P` lies **outside** the digit window `(C-2, C]` (`C = dStepC … d`),
almost every `W` has a step `n` where the `d`-step floor map fails to read a base-2 digit
(`dStepV … − 2⌊W·2ⁿ⌋ ∉ {0,1}`).

This is the full assembly — density (`ae_W_dTorus_orbit_dense`) + continuity (`continuousAt_dGpdTorus`)
+ window confinement (`dStep_partial_mem_window`) via the threshold tools — leaving as its single
hypothesis exactly the **nonzero-coordinate realization** (constructible via `exists_scale_outside_window`
+ `orbitF_realizeR` + a countability choice; see `PENDING_WORK.md`).  Discharging that hypothesis turns
this into the unconditional uniform general-`d` headline. -/
theorem ae_dStep_fails_of_exceeding (d : ℕ) (hd : 1 ≤ d) (c : ℕ → ℝ)
    (P : Fin d → AddCircle (1 : ℝ)) (hne : ∀ i, P i ≠ 0)
    (harg : ∀ k, k < d - 1 →
      orbitArg (rrt d) c (coordsOf d P) k ≠ ((⌊orbitArg (rrt d) c (coordsOf d P) k⌋ : ℤ) : ℝ))
    (hexc : dGpdTorus d (rrt d) c P < dStepC (rrt d) c d - 2 ∨
            dStepC (rrt d) c d < dGpdTorus d (rrt d) c P) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∃ n : ℕ,
      ¬ (dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 0
          ∨ dStepV (rrt d) c (⌊W * 2 ^ n⌋) d - 2 * (⌊W * 2 ^ n⌋ : ℝ) = 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hα : (rrt (e + 1)) ^ (e + 1) = 2 := rrt_pow_self (e + 1) (by omega)
  have hcont : ContinuousAt (dGpdTorus (e + 1) (rrt (e + 1)) c) P :=
    continuousAt_dGpdTorus (e + 1) (rrt (e + 1)) c P hne harg
  filter_upwards [ae_W_dTorus_orbit_dense (d := e + 1) (by omega)] with W hdense
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hwin : ∀ n : ℕ, dStepC (rrt (e + 1)) c (e + 1) - 2
        < dGpdTorus (e + 1) (rrt (e + 1)) c (dTorusOrbit (e + 1) W n)
      ∧ dGpdTorus (e + 1) (rrt (e + 1)) c (dTorusOrbit (e + 1) W n)
        ≤ dStepC (rrt (e + 1)) c (e + 1) := by
    intro n
    rw [dGpdTorus_orbit (e + 1) (by omega)]
    exact dStep_partial_mem_window (rrt (e + 1)) c (⌊W * 2 ^ n⌋) e hα (hcon n)
  rcases hexc with hlt | hgt
  · obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont hlt
    exact absurd (hwin n).1 (not_lt.mpr hn.le)
  · obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont hgt
    exact absurd (hwin n).2 (not_le.mpr hn)

end Erdos482.General
