import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Pi
import Erdos482.General.Equidistribution

/-!
# Multidimensional Weyl criterion (toward step (c): the `T³` lift of the cubic frontier)

`PENDING_WORK.md ★★` step (c) lifts the a.e. doubling equidistribution to the torus
`UnitAddTorus d = d → ℝ/ℤ`.  mathlib's `Mathlib.Analysis.Fourier.AddCircleMulti` already provides the
torus Fourier characters `mFourier` and torus Stone–Weierstrass (`span_mFourier_closure_eq_top`), so the
multidimensional Weyl criterion is a near-mirror of the 1-D `Equidistribution.weyl_criterion`.

This file builds the genuinely-new crux first: **the torus Fourier integral**
`∫ mFourier n = δ_{n,0}` (`integral_mFourier_eq`), via Fubini over the product measure
(`integral_fintype_prod_volume_eq_prod`) and the 1-D `integral_fourier_eq`.
-/

open Filter Finset MeasureTheory UnitAddTorus AddCircle
open scoped Topology

noncomputable section
namespace Erdos482.General

/-- **Integral of a torus Fourier monomial** (product Haar): `∫ mFourier n = 1` if `n = 0` and `0`
otherwise.  By Fubini `∫_{Tᵈ} ∏ᵢ fourier(nᵢ) = ∏ᵢ ∫ fourier(nᵢ) = ∏ᵢ δ_{nᵢ,0} = δ_{n,0}`. -/
theorem integral_mFourier_eq {d : Type*} [Fintype d] (n : d → ℤ) :
    (∫ x : (d → AddCircle (1:ℝ)), mFourier n x ∂volume) = if n = 0 then 1 else 0 := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  have hvh : (volume : Measure (AddCircle (1:ℝ))) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have hfac : ∀ k : ℤ, (∫ y : AddCircle (1:ℝ), fourier k y ∂volume) = if k = 0 then 1 else 0 := by
    intro k; rw [hvh]; exact integral_fourier_eq k
  have hprod : ∀ x : (d → AddCircle (1:ℝ)), mFourier n x = ∏ i, fourier (n i) (x i) := fun _ => rfl
  simp_rw [hprod]
  rw [show (∫ x : (d → AddCircle (1:ℝ)), ∏ i, fourier (n i) (x i) ∂volume)
        = ∏ i, ∫ y : AddCircle (1:ℝ), fourier (n i) y ∂volume from
      integral_fintype_prod_volume_eq_prod (fun i y => fourier (n i) y)]
  simp only [hfac]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end Erdos482.General
