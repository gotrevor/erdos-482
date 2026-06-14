import Erdos482.General.DELEngine
import Erdos482.General.WeylDoubling
import Erdos482.General.Equidistribution

/-!
# Step (b) assembly: a.e. equidistribution of the doubling orbit `{2ⁿ s}`

`PENDING_WORK.md ★★` step (b).  Combining the bricks of this lap —
* `WeylDoubling.doubling_weyl_L2_normalized` (`∫₀¹‖(1/N)∑_{n<N} e(k2ⁿ·)‖² = 1/N`),
* `DELEngine.l2_bridge` + `DELEngine.ae_tendsto_zero_of_summable_sq` (the DEL L² engine),
* `Equidistribution.tsum_ofReal_inv_sq_ne_top` (p-series finiteness),
* `Equidistribution.cesaro_fill_of_subseq_sq` (gap-fill `j²` → all `N`),
* `Equidistribution.weyl_criterion` + `fourier_doubling_eq` (Weyl criterion + the fourier↔exp seam),

we obtain: **for almost every `s ∈ [0,1]`, the doubling orbit `n ↦ ↑(2ⁿ s)` is equidistributed on
`ℝ/ℤ`** (`ae_doubling_orbit_equidistributed`).  This is the unconditional a.e. input that the cubic
self-referential frontier's path #2 lifts to `T³` (step (c)) to break the two-plane defect confinement.
-/

open Filter Finset MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace Erdos482.General

/-- The normalized doubling exponential along the squares, `g_j(s) = (1/j²)∑_{n<j²} e(k·2ⁿ·s)`. -/
private def gWeyl (k : ℤ) (j : ℕ) (s : ℝ) : ℂ :=
  ((j ^ 2 : ℕ) : ℂ)⁻¹ * ∑ n ∈ range (j ^ 2),
    Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)

/-- Each doubling exponential `e(k·2ⁿ·s)` has unit modulus. -/
theorem norm_doubling_exp (k : ℤ) (n : ℕ) (s : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)‖ = 1 := by
  rw [show (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * (s:ℂ))
        = ((2 * Real.pi * (k * 2 ^ n) * s : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Per-frequency a.e. vanishing of the doubling Weyl average.**  For `k ≠ 0`, almost every
`s ∈ [0,1]` has `(1/N)∑_{n<N} e(k·2ⁿ·s) → 0`.  (DEL engine along the squares `j²` — mean square `1/j²`
is summable — then the gap-fill to all `N`.) -/
theorem ae_doubling_weyl_tendsto (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
  have hcont : ∀ j, Continuous (gWeyl k j) := by
    intro j
    unfold gWeyl
    refine continuous_const.mul (continuous_finset_sum _ (fun n _ => ?_))
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hmeas : ∀ j, AEStronglyMeasurable (gWeyl k j) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    fun j => (hcont j).aestronglyMeasurable
  have hL2 : ∀ j, (∫⁻ x in Set.Icc (0:ℝ) 1, ‖gWeyl k j x‖₊ ^ 2 ∂volume)
      = ENNReal.ofReal (((j ^ 2 : ℕ) : ℝ)⁻¹) := by
    intro j
    rw [l2_bridge (gWeyl k j) (hcont j)]
    congr 1
    unfold gWeyl
    exact doubling_weyl_L2_normalized k hk (j ^ 2)
  have hsum : (∑' j, ∫⁻ x in Set.Icc (0:ℝ) 1, ‖gWeyl k j x‖₊ ^ 2 ∂volume) ≠ ⊤ := by
    rw [tsum_congr hL2]; exact tsum_ofReal_inv_sq_ne_top
  filter_upwards [ae_tendsto_zero_of_summable_sq (gWeyl k) hmeas hsum] with s hs
  simp only [gWeyl] at hs
  set a : ℕ → ℂ :=
    fun n => Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s) with ha
  exact cesaro_fill_of_subseq_sq a (fun n => le_of_eq (norm_doubling_exp k n s)) hs

/-- **Step (b) — a.e. equidistribution of the doubling orbit.**  For almost every `s ∈ [0,1]`, the
doubling orbit `n ↦ ↑(2ⁿ·s)` is equidistributed on `ℝ/ℤ`.  Intersect the per-frequency a.e. vanishing
(`ae_doubling_weyl_tendsto`) over the countably many `k ≠ 0` (`ae_all_iff`), then apply Weyl's criterion
(`weyl_criterion`) through the fourier↔exp seam (`fourier_doubling_eq`).  This is the unconditional a.e.
input the cubic frontier's path #2 lifts to `T³` (step (c)). -/
theorem ae_doubling_orbit_equidistributed :
    ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      IsEquidistributed (fun n => (((2:ℝ) ^ n * s : ℝ) : AddCircle (1:ℝ))) := by
  have hk : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N:ℂ)⁻¹ * ∑ n ∈ range N,
          Complex.exp (2 * ↑Real.pi * Complex.I * ((k * (2:ℤ) ^ n : ℤ) : ℂ) * s)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro k
    by_cases hk0 : k = 0
    · exact ae_of_all _ (fun s h => absurd hk0 h)
    · filter_upwards [ae_doubling_weyl_tendsto k hk0] with s hs
      exact fun _ => hs
  filter_upwards [hk] with s hsk
  refine weyl_criterion _ (fun k hk0 => ?_)
  exact (hsk k hk0).congr (fun N => by
    congr 1
    exact Finset.sum_congr rfl (fun n _ => (fourier_doubling_eq k n s).symm))

end Erdos482.General
