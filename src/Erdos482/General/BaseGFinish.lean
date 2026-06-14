import Erdos482.General.GeneralTorusFinish
import Erdos482.General.BaseGTorusEquidist

/-!
# The base-`g` general-degree impossibility (uniform over schedules)

The base-`g` analogue of `GeneralTorusFinish.ae_no_dStep_schedule_reads_base_two`.  For `α = g^{1/d}`
with `g ≥ 2`, an Eisenstein prime for `g` (`p ∣ g`, `p² ∤ g`, giving ℤ-lin-indep of `{1, α, …, α^{d-1}}`),
and the window-escape bound `α < 2g/(g+1)` (which forces the partial-defect window width `S_d > g`,
`geom_window_gt_base`), almost every real `W` admits **no** degree-`d` schedule reading `W`'s base-`g`
digits: for every `c` there is a step `n` where the extracted digit `dStepV(⌊W·gⁿ⌋) − g·⌊W·gⁿ⌋`
leaves `{0, …, g-1}`.

The plumbing (`coordsOf`, `dGpdTorus`, `continuousAt_dGpdTorus`) and the geometry-crux construction
(`realizeR0`, `orbitF_realizeR0`, the countable bad-set seed choice) are all base-agnostic; only the
multiplier `gⁿ`, the window width `S_d > g`, and the digit window `(C − g, C]` differ from base 2.
-/

open Filter MeasureTheory AddCircle
open scoped Topology

noncomputable section
namespace Erdos482.General

/-- **`dGpdTorus` reads the partial defect along the base-`g` orbit**: at seed `W`, step `n`,
`dGpdTorus d (grt g d) c (dTorusOrbitG g d W n) = dStepPartial (grt g d) c (⌊W·gⁿ⌋) d`.  Base-`g`
analogue of `dGpdTorus_orbit`, via the real-multiplier bridge `dStepPartial_eq_dGpd_real` (M = W·gⁿ). -/
theorem dGpdTorusG_orbit (g d : ℕ) (hd : 1 ≤ d) (c : ℕ → ℝ) (W : ℝ) (n : ℕ) :
    dGpdTorus d (grt g d) c (dTorusOrbitG g d W n)
      = dStepPartial (grt g d) c (⌊W * (g : ℝ) ^ n⌋) d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [dGpdTorus, Nat.add_sub_cancel,
    dGpd_congr (grt g (e + 1)) c (coordsOf (e + 1) (dTorusOrbitG g (e + 1) W n))
      (fun i => Int.fract ((grt g (e + 1)) ^ i * (W * (g : ℝ) ^ n))) e ?_,
    ← dStepPartial_eq_dGpd_real]
  intro i hi
  have hid : i < e + 1 := by omega
  simp only [coordsOf, dif_pos hid, dTorusOrbitG, torusRep_coe]
  congr 1
  ring

/-- **The base-`g` geometry crux.**  For `α = g^{1/d}` with `g ≥ 2`, `d ≥ 2`, and the window-escape
bound `α < 2g/(g+1)`, any schedule `c` admits a torus point `P` with all coordinates nonzero, all inner
arguments non-integer, and partial-defect value `dGpdTorus P` strictly outside the digit window
`(C − g, C]` (`C = dStepC … d`).  Base-`g` analogue of `exists_exceeding_torus_point`: window width
`S_d > g` via `geom_window_gt_base`, strict escape via `exists_scale_outside_window_strict_base`. -/
theorem exists_exceeding_torus_point_base (g d : ℕ) (hg : 2 ≤ g) (hd : 2 ≤ d)
    (hbound : grt g d < 2 * (g : ℝ) / ((g : ℝ) + 1)) (c : ℕ → ℝ) :
    ∃ P : Fin d → AddCircle (1 : ℝ), (∀ i, P i ≠ 0)
      ∧ (∀ k, k < d - 1 →
          orbitArg (grt g d) c (coordsOf d P) k
            ≠ ((⌊orbitArg (grt g d) c (coordsOf d P) k⌋ : ℤ) : ℝ))
      ∧ (dGpdTorus d (grt g d) c P < dStepC (grt g d) c d - (g : ℝ) ∨
          dStepC (grt g d) c d < dGpdTorus d (grt g d) c P) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  set α : ℝ := grt g (e + 1) with hαdef
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  have hαpos : 0 < α := rpow_inv_pos (g : ℝ) hgpos (e + 1)
  have hαd : α ^ (e + 1) = (g : ℝ) := rpow_inv_pow_self (g : ℝ) hgpos.le (e + 1) (by omega)
  have hα1 : 1 < α := by
    by_contra hc
    have : α ^ (e + 1) ≤ 1 ^ (e + 1) := pow_le_pow_left₀ hαpos.le (not_lt.mp hc) (e + 1)
    rw [hαd, one_pow] at this
    have : (g : ℝ) ≤ 1 := this
    have : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  -- window width `S > g`
  set S : ℝ := ∑ k ∈ Finset.range e, α ^ (e - k) with hSdef
  have hSsum : S = ∑ j ∈ Finset.Ico 1 (e + 1), α ^ j := by
    rw [hSdef, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      ← Finset.sum_range_reflect (fun k => α ^ (1 + k)) e]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk; congr 1; omega
  have hSgt : (g : ℝ) < S := by
    rw [hSsum]; exact geom_window_gt_base α (e + 1) (g : ℝ) hα1 (by omega) hαd hbound hgpos
  -- the escaping scale `τ`
  obtain ⟨τ, hτ, hτout⟩ :=
    exists_scale_outside_window_strict_base S (dStepC α c (e + 1)) (g : ℝ) hgpos hSgt
  have hτico : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
  -- the countable bad set and the chosen seed `σ`
  set K : ℕ → ℝ := fun k => (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) + α * c k with hKdef
  set gg : ℕ → ℤ → ℝ := fun k m => ((m : ℝ) - τ + K k) / α ^ (k + 1) with hggdef
  set B : Set ℝ := ⋃ k : Fin e, Set.range (gg k.val) with hBdef
  have hBcount : B.Countable := Set.countable_iUnion (fun k => Set.countable_range _)
  have huncount : ¬ (Set.Ioo (0 : ℝ) 1).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]; norm_num
  obtain ⟨σ, hσio, hσB⟩ : ∃ σ, σ ∈ Set.Ioo (0 : ℝ) 1 ∧ σ ∉ B := by
    by_contra hcon; push_neg at hcon
    exact huncount (hBcount.mono (fun x hx => hcon x hx))
  -- the realizer and its coordinate properties
  set r : ℕ → ℝ := realizeR0 α c τ σ with hrdef
  have hr_ico : ∀ i, r i ∈ Set.Ico (0 : ℝ) 1 := by
    intro i
    rw [hrdef]; cases i with
    | zero => exact ⟨hσio.1.le, hσio.2⟩
    | succ k => exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hr_pos : ∀ i, i ≤ e → 0 < r i := by
    intro i hi
    rw [hrdef]
    cases i with
    | zero => exact hσio.1
    | succ k =>
      have hk : k < e := by omega
      have hval : realizeR0 α c τ σ (k + 1)
          = Int.fract (τ + α ^ (k + 1) * σ
              - (∑ j ∈ Finset.range k, α ^ (k - j) * (α * c j - τ)) - α * c k) := rfl
      rw [hval]
      refine lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm ?_)
      rw [Int.fract_ne_zero_iff]
      rintro ⟨m, hm⟩
      apply hσB
      rw [hBdef, Set.mem_iUnion]
      refine ⟨⟨k, hk⟩, m, ?_⟩
      simp only [hggdef, hKdef]
      rw [div_eq_iff (pow_ne_zero (k + 1) (ne_of_gt hαpos))]
      linear_combination hm
  -- the torus point
  set P : Fin (e + 1) → AddCircle (1 : ℝ) := fun i => ((r i.val : ℝ) : AddCircle (1 : ℝ)) with hPdef
  have hcoord : ∀ i, i ≤ e → coordsOf (e + 1) P i = r i := by
    intro i hi
    have hlt : i < e + 1 := by omega
    simp only [coordsOf, dif_pos hlt, hPdef, torusRep_coe]
    exact Int.fract_eq_self.mpr (hr_ico i)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    have hi : i.val ≤ e := Nat.lt_succ_iff.mp i.isLt
    simp only [hPdef, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico (hr_ico i.val)]
    exact (hr_pos i.val hi).ne'
  · intro k hk
    have hF : orbitF α c (coordsOf (e + 1) P) k = τ := by
      rw [orbitF_congr α c (coordsOf (e + 1) P) r k (fun i hi => hcoord i (by omega)), hrdef]
      exact orbitF_realizeR0 α c τ σ hτico k
    intro heq
    have hfr : Int.fract (orbitArg α c (coordsOf (e + 1) P) k) = 0 := by
      rw [heq]; exact Int.fract_intCast _
    rw [← orbitF_eq_fract_arg, hF] at hfr
    exact hτ.1.ne' hfr
  · have hval : dGpdTorus (e + 1) α c P = S * τ := by
      have hterm : ∀ k ∈ Finset.range e,
          α ^ (e - k) * orbitF α c (realizeR0 α c τ σ) k = α ^ (e - k) * τ := by
        intro k _; rw [orbitF_realizeR0 α c τ σ hτico k]
      rw [dGpdTorus, Nat.add_sub_cancel,
        dGpd_congr α c (coordsOf (e + 1) P) r e (fun i hi => hcoord i hi)]
      unfold dGpd
      rw [hrdef, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hSdef]
    rw [hval]
    rcases hτout with h | h
    · exact Or.inl (by rw [mul_comm S τ]; exact h)
    · exact Or.inr (by rw [mul_comm S τ]; exact h)

/-- **The unconditional uniform base-`g` general-`d` impossibility.**  For `α = g^{1/d}` with `g ≥ 2`,
`d ≥ 2`, an Eisenstein prime for `g` (`p ∣ g`, `p² ∤ g`), and the window-escape bound `α < 2g/(g+1)`:
for *almost every* real `W`, **no** degree-`d` schedule `c` makes the `d`-step floor map read `W`'s
base-`g` digits — for every `c` there is a step `n` where the extracted digit
`dStepV(⌊W·gⁿ⌋) − g·⌊W·gⁿ⌋` leaves `{0, …, g-1}`.

Base-`g` analogue of `ae_no_dStep_schedule_reads_base_two`.  The single exceptional null set is the
schedule-independent orbit-density set (`ae_W_dTorusG_orbit_dense_eisenstein`); for each `W` there and
each `c`, `exists_exceeding_torus_point_base` exhibits a non-jump torus point leaving the width-`g` digit
window, and density + continuity realize an out-of-window orbit step, contradicting
`dStep_partial_mem_window_base`. -/
theorem ae_no_dStep_schedule_reads_base_g (g d : ℕ) (hg : 2 ≤ g) (hd : 2 ≤ d)
    (hbound : grt g d < 2 * (g : ℝ) / ((g : ℝ) + 1))
    (p : ℕ) (hp : p.Prime) (hpg : p ∣ g) (hpg2 : ¬ (p ^ 2 ∣ g)) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c : ℕ → ℝ, ∃ n : ℕ,
      ¬ (0 ≤ dStepV (grt g d) c (⌊W * (g : ℝ) ^ n⌋) d - (g : ℝ) * (⌊W * (g : ℝ) ^ n⌋ : ℝ)
          ∧ dStepV (grt g d) c (⌊W * (g : ℝ) ^ n⌋) d - (g : ℝ) * (⌊W * (g : ℝ) ^ n⌋ : ℝ)
              ≤ (g : ℝ) - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  have hα : (grt g (e + 1)) ^ (e + 1) = (g : ℝ) :=
    rpow_inv_pow_self (g : ℝ) hgpos.le (e + 1) (by omega)
  filter_upwards [ae_W_dTorusG_orbit_dense_eisenstein (g := g) (d := e + 1) hg (by omega) hp hpg hpg2]
    with W hdense
  intro c
  obtain ⟨P, hne, harg, hexc⟩ := exists_exceeding_torus_point_base g (e + 1) hg (by omega) hbound c
  have hcont : ContinuousAt (dGpdTorus (e + 1) (grt g (e + 1)) c) P :=
    continuousAt_dGpdTorus (e + 1) (grt g (e + 1)) c P hne harg
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hwin : ∀ n : ℕ, dStepC (grt g (e + 1)) c (e + 1) - (g : ℝ)
        < dGpdTorus (e + 1) (grt g (e + 1)) c (dTorusOrbitG g (e + 1) W n)
      ∧ dGpdTorus (e + 1) (grt g (e + 1)) c (dTorusOrbitG g (e + 1) W n)
        ≤ dStepC (grt g (e + 1)) c (e + 1) := by
    intro n
    rw [dGpdTorusG_orbit g (e + 1) (by omega)]
    exact dStep_partial_mem_window_base (grt g (e + 1)) c (⌊W * (g : ℝ) ^ n⌋) e g hα
      (hcon n).1 (hcon n).2
  rcases hexc with hlt | hgt
  · obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont hlt
    exact absurd (hwin n).1 (not_lt.mpr hn.le)
  · obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont hgt
    exact absurd (hwin n).2 (not_le.mpr hn)

/-- **The window-escape bound is met whenever `g < (2g/(g+1))ᵈ`.**  Raises the integer inequality to the
`1/d` power (`Real.rpow_lt_rpow`): `α = g^{1/d} < ((2g/(g+1))ᵈ)^{1/d} = 2g/(g+1)`.  Base-`g` analogue of
`rrt_lt_four_thirds`; lets the abstract `hbound` of `ae_no_dStep_schedule_reads_base_g` be discharged by
a concrete numeric check per `(g, d)`. -/
theorem grt_lt_bound (g d : ℕ) (hg : 2 ≤ g) (hd : 1 ≤ d)
    (h : (g : ℝ) < (2 * (g : ℝ) / ((g : ℝ) + 1)) ^ d) :
    grt g d < 2 * (g : ℝ) / ((g : ℝ) + 1) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
  set β : ℝ := 2 * (g : ℝ) / ((g : ℝ) + 1) with hβ
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdinv : (0 : ℝ) < (1 : ℝ) / d := by positivity
  have hlt := Real.rpow_lt_rpow hgpos.le h hdinv
  have hrhs : (β ^ d) ^ ((1 : ℝ) / d) = β := by
    rw [← Real.rpow_natCast β d, ← Real.rpow_mul hβpos.le, mul_one_div, div_self hdne, Real.rpow_one]
  rwa [hrhs] at hlt

/-- **Unconditional base-3 general-degree impossibility** (`g = 3`, `d = 3`, `α = 3^{1/3}`).  A fully
discharged instance of `ae_no_dStep_schedule_reads_base_g`: for almost every `W`, no degree-3 schedule
reads `W`'s base-3 digits.  The hypotheses are met — Eisenstein prime `p = 3` (`3 ∣ 3`, `9 ∤ 3`) and the
window bound `3^{1/3} < 3/2` (`3 < (3/2)³ = 27/8`, `grt_lt_bound`). -/
theorem ae_no_dStep_schedule_reads_base_three :
    ∀ᵐ W ∂(volume : Measure ℝ), ∀ c : ℕ → ℝ, ∃ n : ℕ,
      ¬ (0 ≤ dStepV (grt 3 3) c (⌊W * (3 : ℝ) ^ n⌋) 3 - (3 : ℝ) * (⌊W * (3 : ℝ) ^ n⌋ : ℝ)
          ∧ dStepV (grt 3 3) c (⌊W * (3 : ℝ) ^ n⌋) 3 - (3 : ℝ) * (⌊W * (3 : ℝ) ^ n⌋ : ℝ)
              ≤ (3 : ℝ) - 1) := by
  have hbound : grt 3 3 < 2 * (3 : ℝ) / ((3 : ℝ) + 1) :=
    grt_lt_bound 3 3 (by norm_num) (by norm_num) (by norm_num)
  exact ae_no_dStep_schedule_reads_base_g 3 3 (by norm_num) (by norm_num) hbound 3
    (by norm_num) (by norm_num) (by norm_num)

end Erdos482.General
