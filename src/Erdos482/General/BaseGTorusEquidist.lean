import Erdos482.General.BaseGEquidist
import Erdos482.General.MultidimWeyl
import Erdos482.General.EquidistDense
import Erdos482.General.DELEngine

/-!
# a.e.-`W` equidistribution of the base-`g` torus orbit `gⁿ(W, αW, …, α^{d-1}W)`

The base-`g` analogue of `GeneralTorusEquidist` (`α = g^{1/d}`).  For almost every real `W`, the orbit
`n ↦ (gⁿ·αⁱ·W mod 1)_{i<d} ∈ Tᵈ` is **equidistributed**, hence **dense** — *provided* the frequencies
`{1, α, …, α^{d-1}}` are ℤ-linearly independent (`hli`), i.e. `Xᵈ − g` is irreducible over ℚ.

The analytic engine (`MultidimWeyl.weyl_criterion_torus`, `DELEngine.ae_comp_mul_left`,
`BaseGEquidist.ae_baseG_weyl_tendsto_real`) is base- and degree-agnostic; the only per-`(g,d)` input is
the ℤ-linear independence, supplied here as a hypothesis (`hli : ∀ m ≠ 0, ∑ᵢ mᵢαⁱ ≠ 0`) to be discharged
separately (Eisenstein for `g` prime-power-free, or `X_pow_sub_C_irreducible_of_prime` for `d` prime and
`g` not a perfect `d`-th power).
-/

open Filter Finset MeasureTheory UnitAddTorus AddCircle
open scoped Topology

noncomputable section
namespace Erdos482.General

/-- `α = g^{1/d}` (the base-`g` degree-`d` multiplier). -/
abbrev grt (g d : ℕ) : ℝ := (g : ℝ) ^ ((1 : ℝ) / d)

/-- The frequency scalar `ξ = ∑_{i<d} mᵢ·αⁱ` of a torus character `m : Fin d → ℤ` (`α = g^{1/d}`). -/
def dXiG (g d : ℕ) (m : Fin d → ℤ) : ℝ := ∑ i : Fin d, (m i : ℝ) * (grt g d) ^ (i : ℕ)

/-- The base-`g` degree-`d` `Tᵈ` orbit at seed `W`: `n ↦ (gⁿ·αⁱ·W mod 1)_{i<d}`. -/
def dTorusOrbitG (g d : ℕ) (W : ℝ) : ℕ → (Fin d → AddCircle (1 : ℝ)) :=
  fun n i => (((g : ℝ) ^ n * (grt g d) ^ (i : ℕ) * W : ℝ) : AddCircle (1 : ℝ))

/-- **The torus character along the orbit is a frequency-1 base-`g` exponential**:
`mFourier m (orbitₙ) = e(2πi · gⁿ · ξW)`, `ξ = ∑ᵢ mᵢαⁱ`. -/
lemma dmFourierG_orbit_eq (g d : ℕ) (m : Fin d → ℤ) (W : ℝ) (n : ℕ) :
    mFourier m (dTorusOrbitG g d W n)
      = Complex.exp (2 * ↑Real.pi * Complex.I * (((1 : ℤ) * (g : ℤ) ^ n : ℤ) : ℂ)
          * ((dXiG g d m * W : ℝ) : ℂ)) := by
  have hprod : mFourier m (dTorusOrbitG g d W n)
      = ∏ i : Fin d, fourier (m i) (dTorusOrbitG g d W n i) := rfl
  rw [hprod]
  simp_rw [dTorusOrbitG, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [dXiG]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Per-character a.e.-`W` vanishing** (`m ≠ 0`, given lin-indep): the character is the frequency-1
base-`g` sum at `s = ξW`; `ae_baseG_weyl_tendsto_real 1` scaled by `ae_comp_mul_left` (`c = ξ ≠ 0`). -/
lemma ae_W_dmFourierG_orbit_tendsto {g d : ℕ} (hg : 2 ≤ g)
    (hli : ∀ m : Fin d → ℤ, m ≠ 0 → dXiG g d m ≠ 0)
    (m : Fin d → ℤ) (hm : m ≠ 0) :
    ∀ᵐ W ∂(volume : Measure ℝ),
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (dTorusOrbitG g d W n))
        atTop (𝓝 0) := by
  have h := ae_comp_mul_left (hli m hm) (ae_baseG_weyl_tendsto_real hg 1 one_ne_zero)
  filter_upwards [h] with W hW
  refine hW.congr (fun N => ?_)
  refine congrArg _ (Finset.sum_congr rfl (fun n _ => ?_))
  exact (dmFourierG_orbit_eq g d m W n).symm

/-- **a.e.-`W` `Tᵈ` equidistribution** (given lin-indep).  Intersect the per-character vanishing over the
countably many `m ≠ 0` (`ae_all_iff`), then `weyl_criterion_torus`. -/
theorem ae_W_dTorusG_orbit_equidistributed {g d : ℕ} (hg : 2 ≤ g)
    (hli : ∀ m : Fin d → ℤ, m ≠ 0 → dXiG g d m ≠ 0) :
    ∀ᵐ W ∂(volume : Measure ℝ), IsEquidistributedTorus (dTorusOrbitG g d W) := by
  have key : ∀ᵐ W ∂(volume : Measure ℝ), ∀ m : Fin d → ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, mFourier m (dTorusOrbitG g d W n))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : m = 0
    · exact ae_of_all _ (fun W h => absurd hm h)
    · filter_upwards [ae_W_dmFourierG_orbit_tendsto hg hli m hm] with W hW
      exact fun _ => hW
  filter_upwards [key] with W hW
  exact weyl_criterion_torus _ hW

/-- **The base-`g` `Tᵈ` orbit is dense for a.e. `W`** (given lin-indep).  Equidistribution ⇒ dense.  This
is the geometric input that the base-`g` partial-defect window confinement (`dStep_partial_mem_window_base`)
must contradict for the unconditional a.e.-`W` base-`g` impossibility. -/
theorem ae_W_dTorusG_orbit_dense {g d : ℕ} (hg : 2 ≤ g)
    (hli : ∀ m : Fin d → ℤ, m ≠ 0 → dXiG g d m ≠ 0) :
    ∀ᵐ W ∂(volume : Measure ℝ), Dense (Set.range (dTorusOrbitG g d W)) := by
  filter_upwards [ae_W_dTorusG_orbit_equidistributed hg hli] with W hW
  exact isEquidistributedTorus_dense hW

end Erdos482.General
