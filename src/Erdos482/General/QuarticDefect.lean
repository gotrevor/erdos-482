import Mathlib

/-!
# The quartic four-step self-referential floor map (degree-4 generalization, foundations)

Generalizing `CubicDefect` from `α = 2^{1/3}` (3 steps) to `α = 2^{1/4}` (4 steps).  The four-step map
`v₁=⌊α(u+c₀)⌋`, `v₂=⌊α(v₁+c₁)⌋`, `v₃=⌊α(v₂+c₂)⌋`, `v₄=⌊α(v₃+c₃)⌋` reads base-2 digits iff
`v₄ − 2u ∈ {0,1}` for every block `u = ⌊W·2ⁿ⌋` (note `α⁴ = 2`, so four steps multiply by `2`).

This file ports the *algebraic backbone*: the four-step defect identity (`quartic_fourstep_defect`), the
digit bridge (`quarticV4_sub_eq`), and the combined-defect range-width obstruction
(`quartic_combined_defect_range_wide`).  The analytic finish (a.e.-`W` `T⁴` equidistribution + geometry)
reuses the already-general `MultidimWeyl`/`EquidistDense`/`DELEngine` machinery and the
`quartic_lin_indep_int` backbone (in progress); see `PENDING_WORK.md`.
-/

namespace Erdos482.General

open Real

noncomputable section

/-- `α = 2^{1/4}` (the quartic multiplier; `α⁴ = 2`). -/
abbrev qrt2 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)

/-- `qrt2 ^ 4 = 2`. -/
theorem qrt2_quartic : qrt2 ^ 4 = 2 := by
  rw [qrt2, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `1 < qrt2`. -/
theorem one_lt_qrt2 : 1 < qrt2 := by
  rw [qrt2, Real.one_lt_rpow_iff_of_pos (by norm_num)]
  left; constructor <;> norm_num

/-- **The quartic four-step defect identity.**  For any `α` with `α⁴ = 2`, offsets `c₀ c₁ c₂ c₃` and
start `u`, the four-step floor map satisfies
`v₄ = 2u + (2c₀ + α³c₁ + α²c₂ + αc₃) − (α³·f₁ + α²·f₂ + α·f₃ + f₄)`,
where `fᵢ` are the four internal floor errors.  Pure algebra from `α⁴ = 2`. -/
theorem quartic_fourstep_defect (α u c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) :
    let v1 : ℝ := (⌊α * (u + c0)⌋ : ℤ)
    let v2 : ℝ := (⌊α * (v1 + c1)⌋ : ℤ)
    let v3 : ℝ := (⌊α * (v2 + c2)⌋ : ℤ)
    let v4 : ℝ := (⌊α * (v3 + c3)⌋ : ℤ)
    v4 = 2 * u + (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3)
        - (α ^ 3 * Int.fract (α * (u + c0)) + α ^ 2 * Int.fract (α * (v1 + c1))
            + α * Int.fract (α * (v2 + c2)) + Int.fract (α * (v3 + c3))) := by
  intro v1 v2 v3 v4
  have h1 : v1 = α * (u + c0) - Int.fract (α * (u + c0)) := (Int.self_sub_fract _).symm
  have h2 : v2 = α * (v1 + c1) - Int.fract (α * (v1 + c1)) := (Int.self_sub_fract _).symm
  have h3 : v3 = α * (v2 + c2) - Int.fract (α * (v2 + c2)) := (Int.self_sub_fract _).symm
  have h4 : v4 = α * (v3 + c3) - Int.fract (α * (v3 + c3)) := (Int.self_sub_fract _).symm
  linear_combination h4 + α * h3 + α ^ 2 * h2 + α ^ 3 * h1 + (u + c0) * hα

/-- The four-step quartic orbit value `v₄ = ⌊α(⌊α(⌊α(⌊α(u+c₀)⌋+c₁)⌋+c₂)⌋+c₃)⌋` from integer start `u`. -/
noncomputable def quarticV4 (α c0 c1 c2 c3 : ℝ) (u : ℤ) : ℤ :=
  ⌊α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ) + c3)⌋

/-- The combined internal-floor defect `α³f₁ + α²f₂ + αf₃ + f₄` of the four-step map at start `u`. -/
noncomputable def quarticDefect (α c0 c1 c2 c3 : ℝ) (u : ℤ) : ℝ :=
  α ^ 3 * Int.fract (α * ((u : ℝ) + c0))
    + α ^ 2 * Int.fract (α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1))
    + α * Int.fract (α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2))
    + Int.fract (α * (((⌊α * (((⌊α * (((⌊α * ((u : ℝ) + c0)⌋ : ℤ) : ℝ) + c1)⌋ : ℤ) : ℝ) + c2)⌋ : ℤ) : ℝ) + c3))

/-- **Digit bridge.**  The extracted digit `quarticV4 − 2u` equals the schedule constant minus the
combined defect: `(2c₀ + α³c₁ + α²c₂ + αc₃) − quarticDefect`. -/
theorem quarticV4_sub_eq (α c0 c1 c2 c3 : ℝ) (hα : α ^ 4 = 2) (u : ℤ) :
    ((quarticV4 α c0 c1 c2 c3 u : ℤ) : ℝ) - 2 * (u : ℝ)
      = (2 * c0 + α ^ 3 * c1 + α ^ 2 * c2 + α * c3) - quarticDefect α c0 c1 c2 c3 u := by
  have hd := quartic_fourstep_defect α (u : ℝ) c0 c1 c2 c3 hα
  simp only [quarticV4, quarticDefect]
  linarith [hd]

/-- **The combined four-floor defect does not fit any width-2 window** (for any `α > 1`).  As
`(f₁,f₂,f₃,f₄)` ranges over `[0,1)⁴`, the combined defect `α³f₁ + α²f₂ + αf₃ + f₄` cannot be confined to
a closed interval `[C, C+2]` of length 2.  Witnesses `(0,0,0,0) ↦ 0` and `(½,½,½,½) ↦ (α³+α²+α+1)/2`
already differ by more than `2`, since `α³+α²+α+1 > 4` requires only... actually for `α = 2^{1/4} ≈ 1.19`,
`α³+α²+α+1 ≈ 5.28 > 4`.  The clean sufficient bound used here is `1 < α` ⇒ this is the analogue of the
cubic `cubic_combined_defect_range_wide`; a base-2 readout needs the defect in a width-2 window
(`digit ∈ {0,1} ⟺ C−defect ∈ [0,2)`), so a wider range obstructs every fixed schedule. -/
theorem quartic_combined_defect_range_wide (α : ℝ) (hα1 : 1 < α) :
    ¬ ∃ C : ℝ, ∀ f1 f2 f3 f4 : ℝ, 0 ≤ f1 → f1 < 1 → 0 ≤ f2 → f2 < 1 → 0 ≤ f3 → f3 < 1 →
        0 ≤ f4 → f4 < 1 →
      α ^ 3 * f1 + α ^ 2 * f2 + α * f3 + f4 ∈ Set.Icc C (C + 2) := by
  rintro ⟨C, hC⟩
  have h0 := hC 0 0 0 0 le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    (by norm_num)
  have hh := hC (1 / 2) (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Set.mem_Icc] at h0 hh
  -- need α³+α²+α+1 > 4 from α>1; since α>1 ⇒ α³>1, α²>1, α>1, sum+1 > 4
  nlinarith [h0.1, h0.2, hh.1, hh.2, hα1, mul_pos (show (0:ℝ) < α by linarith) (show (0:ℝ) < α by linarith),
    mul_pos (mul_pos (show (0:ℝ) < α by linarith) (show (0:ℝ) < α by linarith))
      (show (0:ℝ) < α by linarith)]

/-- The quartic obstruction is base-`2`, multiplier `2^{1/4}`. -/
theorem quartic_combined_defect_range_wide_qrt2 :
    ¬ ∃ C : ℝ, ∀ f1 f2 f3 f4 : ℝ, 0 ≤ f1 → f1 < 1 → 0 ≤ f2 → f2 < 1 → 0 ≤ f3 → f3 < 1 →
        0 ≤ f4 → f4 < 1 →
      qrt2 ^ 3 * f1 + qrt2 ^ 2 * f2 + qrt2 * f3 + f4 ∈ Set.Icc C (C + 2) :=
  quartic_combined_defect_range_wide qrt2 one_lt_qrt2

end

end Erdos482.General
