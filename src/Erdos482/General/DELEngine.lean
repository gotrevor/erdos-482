import Mathlib

/-!
# The Davenport–Erdős–LeVeque L² engine (Markov + first Borel–Cantelli)

On `[0,1]` with Lebesgue measure: if a sequence of (a.e. strongly) measurable `ℂ`-valued functions
`g_j` has **finite total mean square** `∑_j ∫₀¹ ‖g_j‖² < ∞`, then `g_j → 0` almost everywhere.

This is the abstract analytic step (a) of `PENDING_WORK.md ★★`.  Applied to
`g_j(s) = (1/j²)·∑_{n<j²} e^{2πi k 2ⁿ s}` — whose mean square `∫₀¹‖g_j‖² = 1/j²` (from
`WeylDoubling.doubling_weyl_L2_normalized`) is summable — it yields, along `N_j = j²`,
`(1/N_j)∑_{n<N_j} e(k2ⁿs) → 0` a.e.; gap-filling (`Equidistribution.cesaro_fill_of_subseq_sq`) upgrades
to all `N`, and the Weyl criterion (`Equidistribution.weyl_criterion`) turns that into a.e. base-2
equidistribution of `{2ⁿs}` — the cubic frontier's path #2.

**Provenance.** Proved by Aristotle (job `bd44d316`), verified here in-kernel and `#print axioms`-clean.
Aristotle flagged a genuine **faithfulness bug** in the originally-submitted statement: the hypothesis
`Summable (fun j => ∫⁻ ‖g_j‖₊²)` is *vacuous* (`ENNReal.summable` — every `ℝ≥0∞`-valued function is
`Summable`), so the theorem as first stated was false (the constant `g_j = 1` satisfies it but does not
tend to `0`).  The intended `∑_j ∫₀¹‖g_j‖² < ∞` is the `ℝ≥0∞`-valued total-sum *finiteness*
`(∑' j, ∫⁻ ‖g_j‖₊²) ≠ ⊤`, used below.  (KB: `#print axioms` clean ≠ statement-faithful.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace Erdos482.General

/-- First Borel–Cantelli at a fixed threshold `c`: if the mean squares are summable
(`(∑' j, ∫⁻‖g_j‖₊²) ≠ ⊤`), then for a.e. `x ∈ [0,1]`, eventually `‖g_j x‖₊² < c`.  (Markov bounds each
`μ{x | c ≤ ‖g_j x‖₊²} ≤ (∫⁻‖g_j‖₊²)/c`; the sum is finite, so `μ(limsup) = 0`.) -/
lemma ae_eventually_normSq_lt_of_sum_ne_top
    (g : ℕ → ℝ → ℂ)
    (hmeas : ∀ j, AEStronglyMeasurable (g j) (volume.restrict (Set.Icc (0:ℝ) 1)))
    (hsum : (∑' j, ∫⁻ x in Set.Icc (0:ℝ) 1, ‖g j x‖₊ ^ 2 ∂volume) ≠ ⊤)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      ∀ᶠ j in atTop, (‖g j x‖₊ : ℝ≥0∞) ^ 2 < c := by
  have h_borel_cantelli : (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) (Filter.limsup (fun j => {x | c ≤ (‖(g j x)‖₊ : ℝ≥0∞) ^ 2}) Filter.atTop) = 0 := by
    have h_borel_cantelli : ∀ j, MeasureTheory.volume.restrict (Set.Icc 0 1) {x | c ≤ (‖g j x‖₊ : ℝ≥0∞) ^ 2} ≤ (∫⁻ x in Set.Icc 0 1, (‖g j x‖₊ : ℝ≥0∞) ^ 2) / c := by
      intro j;
      convert MeasureTheory.meas_ge_le_lintegral_div _ _ _ using 1;
      · fun_prop;
      · assumption;
      · assumption;
    convert MeasureTheory.measure_limsup_atTop_eq_zero _;
    · infer_instance;
    · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum h_borel_cantelli ) _ );
      simp_all +decide [ div_eq_mul_inv, ENNReal.tsum_mul_right ];
      exact ENNReal.mul_lt_top ( lt_top_iff_ne_top.mpr hsum ) ( ENNReal.inv_lt_top.mpr ( pos_iff_ne_zero.mpr hc0 ) );
  filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_borel_cantelli ] with x hx;
  simp_all +decide [ Filter.limsup_eq_iInf_iSup_of_nat ]

/-- **Davenport–Erdős–LeVeque L² engine.**  If `∑_j ∫₀¹ ‖g_j‖² < ∞` (as the `ℝ≥0∞` total sum `≠ ⊤`),
then `g_j → 0` almost everywhere on `[0,1]`.  Runs `ae_eventually_normSq_lt_of_sum_ne_top` over the
thresholds `c_k = (1/(k+1))²`, intersects the conull sets, and converts to `Tendsto … (𝓝 0)`. -/
theorem ae_tendsto_zero_of_summable_sq
    (g : ℕ → ℝ → ℂ)
    (hmeas : ∀ j, AEStronglyMeasurable (g j) (volume.restrict (Set.Icc (0:ℝ) 1)))
    (hsum : (∑' j, ∫⁻ x in Set.Icc (0:ℝ) 1, ‖g j x‖₊ ^ 2 ∂volume) ≠ ⊤) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Tendsto (fun j => g j x) atTop (𝓝 0) := by
  have h_bc : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ∀ k : ℕ, ∀ᶠ j in atTop, (‖g j x‖₊ : ℝ≥0∞) ^ 2 < ((k : ℝ≥0∞) + 1)⁻¹ ^ 2 := by
    refine' MeasureTheory.ae_all_iff.2 fun k => _;
    convert ae_eventually_normSq_lt_of_sum_ne_top g hmeas hsum ( ( k + 1 : ℝ≥0∞ ) ⁻¹ ^ 2 ) _ _ using 1 <;> norm_num;
  filter_upwards [ h_bc, MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx hx';
  rw [ Metric.tendsto_nhds ] ; norm_num;
  intro ε hε; rcases exists_nat_one_div_lt hε with ⟨ k, hk ⟩ ; specialize hx k; simp_all +decide ;
  obtain ⟨ a, ha ⟩ := hx; use a; intro b hb; specialize ha b hb; rw [ ← ENNReal.toReal_lt_toReal ] at * <;> norm_num at *;
  exact lt_of_le_of_lt ( Real.le_sqrt_of_sq_le ha.le ) ( by rw [ Real.sqrt_inv, Real.sqrt_sq ( by positivity ) ] ; simpa [ ENNReal.toReal_add, Nat.cast_add_one_ne_zero ] using hk )

end Erdos482.General
