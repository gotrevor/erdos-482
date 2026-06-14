import Erdos482.General.Thm13Closed
import Erdos482.General.Mantissa
import Erdos482.General.St06Example
import Erdos482.General.St06Thm31
import Erdos482.General.St06Thm33
import Erdos482.General.St06Thm34
import Erdos482.General.St06Cor35
import Erdos482.General.SelfRefWall
import Erdos482.General.CubicDefect
import Erdos482.General.DoublingOrbit
import Erdos482.General.WeylDoubling
import Erdos482.General.Equidistribution
import Erdos482.General.DELEngine
import Erdos482.General.DoublingEquidist
import Erdos482.General.MultidimWeyl
import Erdos482.General.EquidistDense
import Erdos482.General.CubicTorusEquidist
import Erdos482.General.CubicDefectLink
import Erdos482.General.CubicFinish
import Erdos482.General.QuarticDefect

/-!
# Erdős–Graham #482 — the general resolution (any `w > 0`, any base `g ≥ 2`)

The headline deliverable of the St05 track, packaged as one statement.  Given any real `w > 0` and any
integer base `g ≥ 2`, there is an explicit floor-recurrence `gu g a b ε` (with `a·b = g`, built from the
base-`g` mantissa `t = w / g^{⌊log_g w⌋} ∈ [1, g)`) whose Graham–Pollak difference
`gu(2n) − g·gu(2n−2)` is exactly the `n`-th base-`g` digit of `w` (as the mathlib digit
`Real.digits (t·g^{n−1}/g) g 0`).  This is Erdős–Graham's "similar results for √m and other algebraic
numbers" — made fully explicit and machine-checked.  Inherits `thm13_digits`: axiom-clean.

We take the offset `ε = −1/g`, which lies in St05's admissible range `[−1/g, (g+1)(g−2)/g)` for **every**
`g ≥ 2` (at `g = 2` the range is `[−1/2, 0)`, so `ε = 0` would fail — `ε = −1/g` is the safe uniform
witness).
-/

namespace Erdos482.General

open Real

/-- **Erdős–Graham #482, resolved in full generality.**  For any `w > 0` and integer base `g ≥ 2`,
with mantissa `t = w/g^{⌊log_g w⌋}`, there exist coefficients `a, b, ε` (with `a·b = g`) so that the
recurrence `gu g a b ε` reads off the base-`g` digits of `w`:
`gu(2n) − g·gu(2n−2) = Real.digits (t·g^{n−1}/g) g 0` for every `n ≥ 1`. -/
theorem erdos482_resolution (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 1 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits
              (w / (g : ℝ) ^ (⌊Real.logb g w⌋) * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by positivity
  have hg1 : (g : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  set t : ℝ := w / (g : ℝ) ^ (⌊Real.logb g w⌋) with ht
  obtain ⟨ht1, ht2⟩ := mantissa_mem g hg w hw
  have htg : t + (g : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ t := ht1; positivity
  refine ⟨(g : ℝ) / (((g : ℝ) - 1) * (t + g)), ((g : ℝ) - 1) * (t + g), -1 / (g : ℝ), ?_, ?_⟩
  · field_simp
  · intro n hn
    have hε0 : -1 / (g : ℝ) ≤ -1 / (g : ℝ) := le_refl _
    have hg2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have hε1 : -1 / (g : ℝ) < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g := by
      rw [div_lt_div_iff_of_pos_right hgpos]
      nlinarith [hg2, mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 2 by linarith)
        (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)]
    exact thm13_digits g hg t ht1 ht2 (-1 / (g : ℝ))
      ((g : ℝ) / (((g : ℝ) - 1) * (t + g))) (((g : ℝ) - 1) * (t + g)) rfl rfl hε0 hε1 n hn

/-- **Erdős–Graham #482 — literal-digit form for `w ∈ [1, g)`.**  When `w` is already its own base-`g`
mantissa (`1 ≤ w < g`), the recurrence reads off `w`'s genuine mathlib base-`g` digits:
`gu(2n) − g·gu(2n−2) = Real.digits w g (n−2)` for every `n ≥ 2`. -/
theorem erdos482_resolution_literal (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ)
    (hw1 : 1 ≤ w) (hw2 : w < (g : ℝ)) :
    ∃ a b ε : ℝ, a * b = (g : ℝ) ∧
      ∀ n, 2 ≤ n →
        gu g a b ε (2 * n) - g * gu g a b ε (2 * n - 2)
          = ((Real.digits w g (n - 2) : ℕ) : ℤ) := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by positivity
  have hg2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (g : ℝ) - 1 ≠ 0 := by linarith
  have htg : w + (g : ℝ) ≠ 0 := by positivity
  refine ⟨(g : ℝ) / (((g : ℝ) - 1) * (w + g)), ((g : ℝ) - 1) * (w + g), -1 / (g : ℝ), by field_simp, ?_⟩
  intro n hn
  have hε1 : -1 / (g : ℝ) < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g := by
    rw [div_lt_div_iff_of_pos_right hgpos]
    nlinarith [hg2, mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 2 by linarith)
      (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)]
  rw [thm13_digits g hg w hw1 hw2 (-1 / (g : ℝ)) _ _ rfl rfl (le_refl _) hε1 n (by omega)]
  exact digit_recon g w (by linarith) n hn

end Erdos482.General
