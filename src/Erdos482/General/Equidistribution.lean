import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Equidistribution framework + Weyl's criterion (toward the a.e.-`W` cubic frontier)

`PENDING_WORK.md ★★` reduces the a.e.-`W` cubic impossibility to **a.e. equidistribution of the doubling
orbit `{2ⁿ s}`**, via Davenport–Erdős–LeVeque (DEL). The DEL chain produces
`(1/N_j)∑_{n<N_j} e(k·2ⁿ s) → 0` a.e. along the subsequence `N_j = j²`; two pieces then assemble the
equidistribution statement, and **neither is in mathlib**:

* **gap-filling** (`cesaro_fill_of_subseq_sq`): from convergence along the squares `N_j = j²` to
  convergence along *all* `N`, using only that the summands are bounded (`‖aₙ‖ ≤ 1`). Elementary, but
  the `Nat.sqrt`-squeeze bookkeeping is the work. Factored through `cesaro_fill_aux`, an abstract
  statement about any sequence of partial sums with `1`-Lipschitz increments.
* **Weyl's criterion** (to come): a sequence on `AddCircle 1` is equidistributed iff all its nonzero
  Weyl sums `(1/N)∑ fourier k` vanish — the `⟸` direction needs Stone–Weierstrass
  (`span_fourier_closure_eq_top`, present in mathlib).
-/

open Filter Finset
open scoped Topology

noncomputable section
namespace Erdos482.General

/-- **Cesàro along squares ⇒ full Cesàro (abstract form).**  For any `S : ℕ → ℂ` whose increments are
`1`-Lipschitz in the counting sense (`‖S n − S m‖ ≤ n − m` for `m ≤ n`): if `(1/j²)·S(j²) → 0` along the
squares, then `(1/N)·S(N) → 0` along all `N`.  The `Nat.sqrt`-squeeze: write `j = ⌊√N⌋`, so
`j² ≤ N < (j+1)²`; then `‖S N‖ ≤ ‖S(j²)‖ + (N−j²) ≤ ‖S(j²)‖ + 2j`, giving
`‖S N‖/N ≤ ‖S(j²)‖/j² + 2/j → 0`. -/
theorem cesaro_fill_aux (S : ℕ → ℂ)
    (hinc : ∀ m n : ℕ, m ≤ n → ‖S n - S m‖ ≤ ((n - m : ℕ) : ℝ))
    (hsub : Tendsto (fun j : ℕ => ((j ^ 2 : ℕ) : ℂ)⁻¹ * S (j ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((N : ℕ) : ℂ)⁻¹ * S N) atTop (𝓝 0) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun b => ⟨b ^ 2, fun N hN => ?_⟩)
    calc b = Nat.sqrt (b ^ 2) := (Nat.sqrt_eq' b).symm
      _ ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN
  refine squeeze_zero_norm (a := fun N : ℕ =>
      ‖((Nat.sqrt N ^ 2 : ℕ) : ℂ)⁻¹ * S (Nat.sqrt N ^ 2)‖ + 2 / (Nat.sqrt N : ℝ))
    (fun N => ?_) ?_
  · -- per-`N` squeeze bound
    show ‖((N : ℕ) : ℂ)⁻¹ * S N‖
        ≤ ‖((Nat.sqrt N ^ 2 : ℕ) : ℂ)⁻¹ * S (Nat.sqrt N ^ 2)‖ + 2 / (Nat.sqrt N : ℝ)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · set j := Nat.sqrt N with hj
      have hjsq_le : j ^ 2 ≤ N := Nat.sqrt_le' N
      have hN_lt : N < (j + 1) ^ 2 := Nat.lt_succ_sqrt' N
      have hjpos : 0 < j := Nat.sqrt_pos.mpr hN
      have hNR : (0:ℝ) < N := by exact_mod_cast hN
      have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hjpos
      have hjsqR : (0:ℝ) < (j:ℝ) ^ 2 := by positivity
      have hjsq_leR : ((j:ℝ)) ^ 2 ≤ (N:ℝ) := by exact_mod_cast hjsq_le
      have hgap : (N - j ^ 2 : ℕ) ≤ 2 * j := by
        have hle : N ≤ (j + 1) ^ 2 - 1 := Nat.le_sub_one_of_lt hN_lt
        have hexp : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
        omega
      have hgapR : ((N - j ^ 2 : ℕ) : ℝ) ≤ 2 * (j:ℝ) := by exact_mod_cast hgap
      have key : ‖S N‖ ≤ ‖S (j ^ 2)‖ + 2 * (j:ℝ) := by
        have h1 : ‖S N - S (j ^ 2)‖ ≤ ((N - j ^ 2 : ℕ) : ℝ) := hinc (j ^ 2) N hjsq_le
        calc ‖S N‖ = ‖S (j ^ 2) + (S N - S (j ^ 2))‖ := by ring_nf
          _ ≤ ‖S (j ^ 2)‖ + ‖S N - S (j ^ 2)‖ := norm_add_le _ _
          _ ≤ ‖S (j ^ 2)‖ + 2 * (j:ℝ) := by linarith
      have e1 : ‖((j ^ 2 : ℕ) : ℂ)⁻¹ * S (j ^ 2)‖ = ‖S (j ^ 2)‖ / ((j:ℝ) ^ 2) := by
        rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
        congr 1
        push_cast; ring
      rw [norm_mul, norm_inv, Complex.norm_natCast, e1]
      have hNinv : (N:ℝ)⁻¹ ≤ ((j:ℝ) ^ 2)⁻¹ := inv_anti₀ hjsqR hjsq_leR
      calc (N:ℝ)⁻¹ * ‖S N‖
          ≤ ((j:ℝ) ^ 2)⁻¹ * (‖S (j ^ 2)‖ + 2 * (j:ℝ)) :=
            mul_le_mul hNinv key (norm_nonneg _) (by positivity)
        _ = ‖S (j ^ 2)‖ / ((j:ℝ) ^ 2) + 2 / (j:ℝ) := by
            have hjne : (j:ℝ) ≠ 0 := ne_of_gt hjR
            field_simp
  · -- the squeeze bound tends to `0`
    have h1 : Tendsto (fun N : ℕ => ‖((Nat.sqrt N ^ 2 : ℕ) : ℂ)⁻¹ * S (Nat.sqrt N ^ 2)‖)
        atTop (𝓝 0) := by
      have hnorm : Tendsto (fun j : ℕ => ‖((j ^ 2 : ℕ) : ℂ)⁻¹ * S (j ^ 2)‖) atTop (𝓝 0) := by
        simpa using hsub.norm
      exact hnorm.comp hsqrt
    have h2 : Tendsto (fun N : ℕ => 2 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun j : ℕ => (2:ℝ) / (j:ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 2
      exact hc.comp hsqrt
    simpa using h1.add h2

/-- **Gap-filling / Cesàro along squares ⇒ full Cesàro.**  If the partial sums `S N = ∑_{n<N} aₙ` of a
bounded sequence (`‖aₙ‖ ≤ 1`) satisfy `(1/j²)·S(j²) → 0` along the squares, then `(1/N)·S(N) → 0` along
*all* `N`.  This is the "fill the gaps between `N_j = j²` and `N_{j+1} = (j+1)²` via `|S_{N+1}−S_N| ≤ 1`"
step of the DEL assembly (`PENDING_WORK.md ★★` step (b)): along the squares the normalized Weyl sum is
`1/j²` (summable ⇒ `→ 0` a.e. by the DEL engine), and this lemma upgrades that to all `N`. -/
theorem cesaro_fill_of_subseq_sq (a : ℕ → ℂ) (hb : ∀ n, ‖a n‖ ≤ 1)
    (hsub : Tendsto (fun j : ℕ => ((j ^ 2 : ℕ) : ℂ)⁻¹ * ∑ n ∈ range (j ^ 2), a n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ range N, a n) atTop (𝓝 0) := by
  refine cesaro_fill_aux (fun N => ∑ n ∈ range N, a n) (fun m n hmn => ?_) hsub
  have hdiff : (∑ k ∈ range n, a k) - (∑ k ∈ range m, a k) = ∑ k ∈ Finset.Ico m n, a k :=
    (Finset.sum_Ico_eq_sub a hmn).symm
  rw [hdiff]
  calc ‖∑ k ∈ Finset.Ico m n, a k‖ ≤ ∑ k ∈ Finset.Ico m n, ‖a k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico m n, (1:ℝ) := Finset.sum_le_sum (fun k _ => hb k)
    _ = ((n - m : ℕ) : ℝ) := by simp

end Erdos482.General
