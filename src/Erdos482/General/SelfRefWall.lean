import Erdos482.Crux

/-!
# The self-referential digit crux is exactly the √2 / base-2 phenomenon

**Context.** The headline Graham–Pollak result rests on `Erdos482.crux`: the *self-referential*
inequality `0 ≤ {x} − √2·{x/2} + √2/2 < 1`, where the recurrence's own coefficient `√2` equals the
algebraic generator of the number whose digits it reads.  A natural question (cf.
`notes/CUBIC-EXPLORATION.md`): does this self-reference generalize to other bases `g` — i.e. does
`u ↦ ⌊√g·(u + c)⌋` read base-`g` digits, via a `g`-analogue crux

> `0 ≤ {x} − √g·{x/g} + c·√g < 1`   for all `x`?

**Answer: NO for every `g ≥ 3`, for ANY offset `c`** (`selfref_crux_fails_of_three_le`).  Combined
with `Erdos482.crux` (the `g = 2`, `c = ½` case) this pins the phenomenon down completely: the elegant
self-referential digit extraction exists **iff `g = 2`** — it is a genuinely quadratic, base-2
miracle, not the tip of a tower of base-`g` analogues.  (Stoll's general St05/St06 results read *any*
real's base-`g` digits, but with a `w`-tuned rational coefficient, never the self-referential `√g`.)

**Proof idea.**  Two witnesses pin `c` between incompatible bounds when `g ≥ 3`:
* `x = g − 1`  has `{x} = 0`, `{x/g} = (g−1)/g`, so the lower bound forces `c·√g ≥ √g·(g−1)/g`,
  i.e. `c ≥ (g−1)/g`;
* `x = ½`  has `{x} = ½`, `{x/g} = 1/(2g)`, so the upper bound needs `½ − √g/(2g) + c·√g < 1`.
Substituting `c ≥ (g−1)/g` and `√g·√g = g` reduces the two to `2g − √g − 3 < 0`, which is false for
`g ≥ 3` (there `√g < g`, so `2g − √g − 3 > g − 3 ≥ 0`).  No `c` survives.
-/

namespace Erdos482.General

open Real

/-- **The self-referential crux fails for every base `g ≥ 3`.**  For each integer `g ≥ 3` and each
offset `c`, there is a real `x` for which the `g`-analogue crux
`0 ≤ {x} − √g·{x/g} + c·√g < 1` is violated.  So no `u ↦ ⌊√g·(u + c)⌋` recurrence can read base-`g`
digits the way `⌊√2·(u + ½)⌋` reads base-2 digits.  (`g = 2`, `c = ½` is `Erdos482.crux`.) -/
theorem selfref_crux_fails_of_three_le (g : ℕ) (hg : 3 ≤ g) (c : ℝ) :
    ∃ x : ℝ, ¬ (0 ≤ Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g ∧
        Int.fract x - Real.sqrt g * Int.fract (x / g) + c * Real.sqrt g < 1) := by
  -- `s = √g` facts
  set s : ℝ := Real.sqrt g with hsdef
  have hgR3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgRpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgRpos
  have hs2 : s ^ 2 = (g : ℝ) := Real.sq_sqrt (le_of_lt hgRpos)
  have hspos : 0 < s := Real.sqrt_pos.mpr hgRpos
  have hs_gt1 : 1 < s := by nlinarith [hs2, hgR3, hspos]
  have hs_lt_g : s < (g : ℝ) := by nlinarith [hs2, mul_pos hspos (show (0 : ℝ) < s - 1 by linarith)]
  by_contra h
  push_neg at h
  -- witness A : x = g − 1  ⇒  lower bound forces  s·(g−1) ≤ c·s·g
  have hA := h ((g : ℝ) - 1)
  have hfA1 : Int.fract ((g : ℝ) - 1) = 0 := by
    have heq : ((g : ℝ) - 1) = ((g - 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ g := by omega
      push_cast [h1]; ring
    rw [heq, Int.fract_natCast]
  have hfA2 : Int.fract (((g : ℝ) - 1) / g) = ((g : ℝ) - 1) / g := by
    apply Int.fract_eq_self.mpr
    refine ⟨div_nonneg (by linarith) (le_of_lt hgRpos), ?_⟩
    rw [div_lt_one hgRpos]; linarith
  rw [hfA1, hfA2] at hA
  have hA' : s * (((g : ℝ) - 1) / g) ≤ c * s := by linarith [hA.1]
  have hAg : s * ((g : ℝ) - 1) ≤ c * s * g := by
    rw [show s * (((g : ℝ) - 1) / g) = (s * ((g : ℝ) - 1)) / g by ring, div_le_iff₀ hgRpos] at hA'
    linarith [hA']
  -- witness B : x = 1/2  ⇒  upper bound  g − s + 2·c·s·g < 2g
  have hB := h (1 / 2)
  have hfB1 : Int.fract ((1 : ℝ) / 2) = 1 / 2 := Int.fract_eq_self.mpr (by constructor <;> norm_num)
  have hfB2 : Int.fract ((1 / 2 : ℝ) / g) = (1 / 2 : ℝ) / g := by
    apply Int.fract_eq_self.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hgRpos]; linarith
  rw [hfB1, hfB2] at hB
  have hB' : (g : ℝ) - s + 2 * (c * s * g) < 2 * g := by
    have heq : (1 / 2 - s * ((1 / 2 : ℝ) / g) + c * s) * (2 * g)
        = (g : ℝ) - s + 2 * (c * s * g) := by field_simp
    have h2g : (0 : ℝ) < 2 * g := by linarith
    nlinarith [mul_lt_mul_of_pos_right hB.2 h2g, heq]
  -- combine:  2·(s·g) − 3s − g < 0, then  2g − s − 3 < 0, false for g ≥ 3
  have hlin : 2 * (s * g) - 3 * s - (g : ℝ) < 0 := by nlinarith [hAg, hB']
  have hkey : 2 * (g : ℝ) - s - 3 < 0 := by
    by_contra hcon
    push_neg at hcon
    have hmul : 0 ≤ s * (2 * (g : ℝ) - s - 3) := mul_nonneg (le_of_lt hspos) hcon
    nlinarith [hmul, hlin, hs2]
  nlinarith [hkey, hs_lt_g, hgR3]

end Erdos482.General
