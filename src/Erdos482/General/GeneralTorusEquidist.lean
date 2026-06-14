import Erdos482.General.DoublingEquidist
import Erdos482.General.MultidimWeyl
import Erdos482.General.EquidistDense
import Erdos482.General.DELEngine
import Erdos482.General.RpowLinIndep

/-!
# a.e.-`W` equidistribution of the general `Tᵈ` orbit `2ⁿ(W, αW, …, α^{d-1}W)`

The degree-`d` analogue of `CubicTorusEquidist` (`α = 2^{1/d}`): for almost every real `W`, the orbit
`n ↦ (2ⁿ·αⁱ·W mod 1)_{i<d} ∈ Tᵈ` is **equidistributed**, hence **dense**.  The analytic engine
(`MultidimWeyl.weyl_criterion_torus`, `DELEngine.ae_comp_mul_left`,
`DoublingEquidist.ae_doubling_weyl_tendsto_real`) is already degree-agnostic; the only per-degree input
is the ℤ-linear independence `rpow_lin_indep_int` (⇒ `ξ = ∑ᵢ mᵢαⁱ ≠ 0` for `m ≠ 0`).
-/

open Filter Finset MeasureTheory UnitAddTorus AddCircle
open scoped Topology

noncomputable section
namespace Erdos482.General

/-- `α = 2^{1/d}` (the degree-`d` multiplier). -/
abbrev rrt (d : ℕ) : ℝ := (2 : ℝ) ^ ((1 : ℝ) / d)

/-- The frequency scalar `ξ = ∑_{i<d} mᵢ·αⁱ` of a torus character `m : Fin d → ℤ`.  Nonzero for
`m ≠ 0` (`rpow_lin_indep_int`). -/
def dXi (d : ℕ) (m : Fin d → ℤ) : ℝ := ∑ i : Fin d, (m i : ℝ) * (rrt d) ^ (i : ℕ)

/-- The degree-`d` `Tᵈ` orbit at seed `W`: `n ↦ (2ⁿ·αⁱ·W mod 1)_{i<d}`. -/
def dTorusOrbit (d : ℕ) (W : ℝ) : ℕ → (Fin d → AddCircle (1 : ℝ)) :=
  fun n i => (((2 : ℝ) ^ n * (rrt d) ^ (i : ℕ) * W : ℝ) : AddCircle (1 : ℝ))

/-- **The torus character along the orbit is a frequency-1 doubling exponential**:
`mFourier m (orbitₙ) = e(2πi · 2ⁿ · ξW)`, `ξ = ∑ᵢ mᵢαⁱ`. -/
lemma dmFourier_orbit_eq (d : ℕ) (m : Fin d → ℤ) (W : ℝ) (n : ℕ) :
    mFourier m (dTorusOrbit d W n)
      = Complex.exp (2 * ↑Real.pi * Complex.I * (((1 : ℤ) * (2 : ℤ) ^ n : ℤ) : ℂ)
          * ((dXi d m * W : ℝ) : ℂ)) := by
  have hprod : mFourier m (dTorusOrbit d W n)
      = ∏ i : Fin d, fourier (m i) (dTorusOrbit d W n i) := rfl
  rw [hprod]
  simp_rw [dTorusOrbit, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [dXi]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The frequency scalar is nonzero for any nonzero `m` (`rpow_lin_indep_int`). -/
lemma dXi_ne_zero {d : ℕ} (hd : 1 ≤ d) {m : Fin d → ℤ} (hm : m ≠ 0) : dXi d m ≠ 0 := by
  intro h
  have hlin := rpow_lin_indep_int d hd m (by rw [dXi] at h; exact h)
  exact hm (funext hlin)

/-- **Per-character a.e.-`W` vanishing** (`m ≠ 0`): the character is the frequency-1 doubling sum at
`s = ξW`; `ae_doubling_weyl_tendsto_real 1` scaled by `ae_comp_mul_left` (`c = ξ ≠ 0`). -/
lemma ae_W_dmFourier_orbit_tendsto {d : ℕ} (hd : 1 ≤ d) (m : Fin d → ℤ) (hm : m ≠ 0) :
    ∀ᵐ W ∂(volume : Measure ℝ),
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (dTorusOrbit d W n))
        atTop (𝓝 0) := by
  have h := ae_comp_mul_left (dXi_ne_zero hd hm) (ae_doubling_weyl_tendsto_real 1 one_ne_zero)
  filter_upwards [h] with W hW
  refine hW.congr (fun N => ?_)
  refine congrArg _ (Finset.sum_congr rfl (fun n _ => ?_))
  exact (dmFourier_orbit_eq d m W n).symm

/-- **a.e.-`W` `Tᵈ` equidistribution.**  Intersect the per-character vanishing over the countably many
`m ≠ 0` (`ae_all_iff`), then `weyl_criterion_torus`. -/
theorem ae_W_dTorus_orbit_equidistributed {d : ℕ} (hd : 1 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), IsEquidistributedTorus (dTorusOrbit d W) := by
  have key : ∀ᵐ W ∂(volume : Measure ℝ), ∀ m : Fin d → ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (dTorusOrbit d W n))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : m = 0
    · exact ae_of_all _ (fun W h => absurd hm h)
    · filter_upwards [ae_W_dmFourier_orbit_tendsto hd m hm] with W hW
      exact fun _ => hW
  filter_upwards [key] with W hW
  exact weyl_criterion_torus _ hW

/-- **The general `Tᵈ` orbit is dense for a.e. `W`.**  Equidistribution ⇒ dense.  This is the geometric
input that the partial-defect window confinement (`dStep_partial_mem_window`) must contradict for the
unconditional a.e.-`W` general-`d` impossibility. -/
theorem ae_W_dTorus_orbit_dense {d : ℕ} (hd : 1 ≤ d) :
    ∀ᵐ W ∂(volume : Measure ℝ), Dense (Set.range (dTorusOrbit d W)) := by
  filter_upwards [ae_W_dTorus_orbit_equidistributed hd] with W hW
  exact isEquidistributedTorus_dense hW

end Erdos482.General
