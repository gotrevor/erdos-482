import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The general degree-`d` defect identity

**Context (the general-`d` self-referential frontier).**  `CubicDefect.lean` / `QuarticDefect.lean`
proved, for `d = 3, 4`, that the `d`-step floor map
`vₖ₊₁ = ⌊α(vₖ + cₖ)⌋`  (`α = 2^{1/d}`, `v₀ = u`)
satisfies the *defect identity*
`v_d = 2u + C − D`,  `C = ∑_{k<d} α^{d-k} cₖ`,  `D = ∑_{k<d} α^{d-1-k} fₖ`,  `fₖ = {α(vₖ+cₖ)}`,
by an explicit `linear_combination` of the `d` floor equations.  That cannot be written down for a
*variable* `d`.

**This file proves the defect identity uniformly for every `d`** (`dStep_defect_identity`).  The clean
generalization is to recognize the floor map as an **affine recurrence** `vₖ₊₁ = α·vₖ + bₖ` with
`bₖ = α cₖ − fₖ`, whose closed form `v_d = αᵈ·v₀ + ∑_{k<d} α^{d-1-k} bₖ` (`affine_rec_closed`) is a
one-line induction.  Substituting `αᵈ = 2` and splitting `bₖ` recovers the identity.

This is the degree-agnostic replacement for the hand-rolled cubic/quartic `linear_combination`s, and
the algebraic backbone for the uniform general-`d` impossibility (paired with `rpow_lin_indep_int` and
`rrt_window_gt_two`).  Everything depends only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos482.General

open Finset

/-- **Closed form of an affine recurrence.**  If `v (k+1) = α·v k + b k` for all `k`, then
`v d = αᵈ·v 0 + ∑_{k<d} α^{d-1-k}·b k`.  One-line induction; the engine behind the general defect
identity. -/
theorem affine_rec_closed (α : ℝ) (v b : ℕ → ℝ) (hrec : ∀ k, v (k + 1) = α * v k + b k) (d : ℕ) :
    v d = α ^ d * v 0 + ∑ k ∈ Finset.range d, α ^ (d - 1 - k) * b k := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [hrec n, ih, Finset.sum_range_succ, pow_succ]
    have hstep : ∀ k ∈ Finset.range n,
        α ^ (n + 1 - 1 - k) * b k = α * (α ^ (n - 1 - k) * b k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have he : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [he, pow_succ]; ring
    have hlast : α ^ (n + 1 - 1 - n) = 1 := by
      have : n + 1 - 1 - n = 0 := by omega
      rw [this, pow_zero]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hlast]
    ring

/-- The `d`-step floor orbit from an integer start `u`: `v₀ = u`, `vₖ₊₁ = ⌊α(vₖ + cₖ)⌋`. -/
noncomputable def dStepV (α : ℝ) (c : ℕ → ℝ) (u : ℤ) : ℕ → ℝ
  | 0 => (u : ℝ)
  | (k + 1) => ((⌊α * (dStepV α c u k + c k)⌋ : ℤ) : ℝ)

/-- The `k`-th internal floor error `fₖ = {α(vₖ + cₖ)}`. -/
noncomputable def dStepF (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (k : ℕ) : ℝ :=
  Int.fract (α * (dStepV α c u k + c k))

/-- **The integer output of the `d`-step floor map** `⌊α(v_{d-1} + c_{d-1})⌋` (`= v_d` for `d ≥ 1`).
The final step is a floor, so `v_d` is an integer; `dStepZ` names that integer.  Used for the genuine
self-referential recurrence `orbit(n+1) = dStepZ(orbit n)`. -/
noncomputable def dStepZ (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (d : ℕ) : ℤ :=
  ⌊α * (dStepV α c u (d - 1) + c (d - 1))⌋

/-- `dStepZ` casts back to `dStepV` (for `d ≥ 1`): the last step of `dStepV` *is* the floor `dStepZ`. -/
theorem dStepZ_cast (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    ((dStepZ α c u d : ℤ) : ℝ) = dStepV α c u d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [dStepZ, Nat.add_sub_cancel, dStepV]

/-- The schedule constant `C = ∑_{k<d} α^{d-k}·cₖ`. -/
noncomputable def dStepC (α : ℝ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range d, α ^ (d - k) * c k

/-- The combined internal-floor defect `D = ∑_{k<d} α^{d-1-k}·fₖ`. -/
noncomputable def dStepDefect (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range d, α ^ (d - 1 - k) * dStepF α c u k

/-- The one-step relation `vₖ₊₁ = α(vₖ + cₖ) − fₖ`. -/
theorem dStepV_succ (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (k : ℕ) :
    dStepV α c u (k + 1) = α * dStepV α c u k + (α * c k - dStepF α c u k) := by
  have h : dStepV α c u (k + 1) = α * (dStepV α c u k + c k) - dStepF α c u k := by
    rw [dStepF]; rw [dStepV]; rw [Int.self_sub_fract]
  rw [h]; ring

/-- **The base-`g` defect identity.**  For any `α` with `αᵈ = g`, schedule `c` and integer start `u`,
the `d`-step floor map satisfies `v_d = g·u + C − D`.  Base-2 (`dStep_defect_identity`) is the `g = 2`
instance; the base-`g` brick for the base-`g` generalization of the impossibility (a base-`g` digit is
`v_d − g·u`, confined to a width-`g` window).  Same proof — the `g` enters only through `hα`. -/
theorem dStep_defect_identity_base (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (d : ℕ) (g : ℝ) (hα : α ^ d = g) :
    dStepV α c u d = g * (u : ℝ) + dStepC α c d - dStepDefect α c u d := by
  have hclosed := affine_rec_closed α (dStepV α c u) (fun k => α * c k - dStepF α c u k)
    (dStepV_succ α c u) d
  rw [hclosed]
  -- v 0 = u, and α^d = g.
  have hv0 : dStepV α c u 0 = (u : ℝ) := by rw [dStepV]
  rw [hv0, hα, dStepC, dStepDefect]
  -- split `∑ α^{d-1-k}(α cₖ − fₖ) = ∑ α^{d-k} cₖ − ∑ α^{d-1-k} fₖ`.
  rw [show (∑ k ∈ Finset.range d, α ^ (d - 1 - k) * (α * c k - dStepF α c u k))
      = (∑ k ∈ Finset.range d, α ^ (d - k) * c k)
          - ∑ k ∈ Finset.range d, α ^ (d - 1 - k) * dStepF α c u k from ?_]
  · ring
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    have he : d - k = (d - 1 - k) + 1 := by omega
    rw [he, pow_succ]; ring

/-- The base-2 defect identity `v_d = 2u + C − D` — the `g = 2` instance of `dStep_defect_identity_base`,
the degree-agnostic version of `cubic_threestep_defect`. -/
theorem dStep_defect_identity (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (d : ℕ) (hα : α ^ d = 2) :
    dStepV α c u d = 2 * (u : ℝ) + dStepC α c d - dStepDefect α c u d :=
  dStep_defect_identity_base α c u d 2 hα

/-- The **partial defect** `g = ∑_{k<d-1} α^{d-1-k} fₖ` — the combined defect minus its last
(forced) term `f_{d-1}`.  (`d = e+1`: `g = D − f_e`.)  The general analogue of `cubicPartialDefect`. -/
noncomputable def dStepPartial (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (d : ℕ) : ℝ :=
  dStepDefect α c u d - dStepF α c u (d - 1)

/-- **The partial defect in explicit sum form**: `g = ∑_{k<e} α^{e-k} fₖ` (`d = e+1`).  Unfolds the
`dStepPartial = D − f_e` definition (the last term of `D`, `α^0 f_e = f_e`, cancels).  This is the form
the realization/window lemmas (`sum_pos_coeff_realize`, `exists_partial_defect_outside_window`) consume,
bridging the defect engine to the geometry. -/
theorem dStepPartial_eq_sum (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) :
    dStepPartial α c u (e + 1) = ∑ k ∈ Finset.range e, α ^ (e - k) * dStepF α c u k := by
  rw [dStepPartial, Nat.add_sub_cancel, dStepDefect, Finset.sum_range_succ]
  have hlast : α ^ (e + 1 - 1 - e) = 1 := by rw [show e + 1 - 1 - e = 0 by omega, pow_zero]
  rw [hlast, one_mul, add_sub_cancel_right]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [show e + 1 - 1 - k = e - k by omega]

/-- **The partial defect is nonnegative** (each `α^{e-k} ≥ 0`, `fₖ = {…} ≥ 0`). -/
theorem dStepPartial_nonneg (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) (hα : 0 ≤ α) :
    0 ≤ dStepPartial α c u (e + 1) := by
  rw [dStepPartial_eq_sum]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hα _) (Int.fract_nonneg _))

/-- **The partial defect stays below the window width** `S_d = ∑_{k<e} α^{e-k}` (`= ∑_{1≤j<d} α^j`):
each `fₖ < 1` and `α^{e-k} > 0`.  So the orbit's partial defect always lies in `[0, S_d)`; for `d ≥ 3`
`S_d > 2` (`rrt_window_gt_two`), so a dense orbit must leave any width-2 digit window. -/
theorem dStepPartial_lt_window (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) (hα : 0 < α) (he : 0 < e) :
    dStepPartial α c u (e + 1) < ∑ k ∈ Finset.range e, α ^ (e - k) := by
  rw [dStepPartial_eq_sum]
  refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) (fun k _ => ?_)
  exact mul_lt_of_lt_one_right (pow_pos hα _) (Int.fract_lt_one _)

/-- **The argument of the last floor is `(C − g) + 2u`.**  Because `α(v_e + c_e) = v_{e+1} + f_e` and
the defect identity gives `v_{e+1} = 2u + C − D = 2u + C − (g + f_e)`.  The kernel of the g-collapse. -/
theorem dStep_last_arg (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) (hα : α ^ (e + 1) = 2) :
    α * (dStepV α c u e + c e)
      = (dStepC α c (e + 1) - dStepPartial α c u (e + 1)) + 2 * (u : ℝ) := by
  have hid := dStep_defect_identity α c u (e + 1) hα
  have hve1 : dStepV α c u (e + 1) = ((⌊α * (dStepV α c u e + c e)⌋ : ℤ) : ℝ) := by rw [dStepV]
  have harg : α * (dStepV α c u e + c e) = dStepV α c u (e + 1) + dStepF α c u e := by
    rw [dStepF, hve1]; exact (Int.floor_add_fract _).symm
  have hdg : dStepDefect α c u (e + 1) = dStepPartial α c u (e + 1) + dStepF α c u e := by
    rw [dStepPartial, Nat.add_sub_cancel]; ring
  rw [harg, hid, hdg]; ring

/-- **The last floor error is forced**: `f_e = {C − g}`.  General analogue of `cubic_f3_eq`. -/
theorem dStep_last_fract_forced (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) (hα : α ^ (e + 1) = 2) :
    dStepF α c u e = Int.fract (dStepC α c (e + 1) - dStepPartial α c u (e + 1)) := by
  rw [dStepF, dStep_last_arg α c u e hα,
    show 2 * (u : ℝ) = ((2 * u : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]

/-- **The extracted digit is a floor of the partial defect**: `v_{e+1} − 2u = ⌊C − g⌋`.
General analogue of `cubic_digit_eq_floor`. -/
theorem dStep_digit_eq_floor (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) (hα : α ^ (e + 1) = 2) :
    dStepV α c u (e + 1) - 2 * (u : ℝ)
      = ((⌊dStepC α c (e + 1) - dStepPartial α c u (e + 1)⌋ : ℤ) : ℝ) := by
  have hid := dStep_defect_identity α c u (e + 1) hα
  have hf := dStep_last_fract_forced α c u e hα
  have hdg : dStepDefect α c u (e + 1) = dStepPartial α c u (e + 1) + dStepF α c u e := by
    rw [dStepPartial, Nat.add_sub_cancel]; ring
  rw [hid, hdg, hf]
  rw [show 2 * (u : ℝ) + dStepC α c (e + 1)
        - (dStepPartial α c u (e + 1)
            + Int.fract (dStepC α c (e + 1) - dStepPartial α c u (e + 1))) - 2 * (u : ℝ)
      = (dStepC α c (e + 1) - dStepPartial α c u (e + 1))
        - Int.fract (dStepC α c (e + 1) - dStepPartial α c u (e + 1)) by ring]
  exact Int.self_sub_fract _

/-- **A base-2 digit confines the partial defect to a width-2 window** `(C − 2, C]`.  If the `d`-step
map reads a base-2 digit (`v_{e+1} − 2u ∈ {0,1}`) then `g ∈ (C − 2, C]`.  Combined with
`rrt_window_gt_two` (the partial-defect range `[0, α+…+α^{d-1})` has width `> 2` for `d ≥ 3`), a dense
orbit must leave this window — the general-`d` obstruction.  Analogue of
`cubic_partial_defect_mem_window`. -/
theorem dStep_partial_mem_window (α : ℝ) (c : ℕ → ℝ) (u : ℤ) (e : ℕ) (hα : α ^ (e + 1) = 2)
    (hdig : dStepV α c u (e + 1) - 2 * (u : ℝ) = 0 ∨ dStepV α c u (e + 1) - 2 * (u : ℝ) = 1) :
    dStepC α c (e + 1) - 2 < dStepPartial α c u (e + 1)
      ∧ dStepPartial α c u (e + 1) ≤ dStepC α c (e + 1) := by
  rw [dStep_digit_eq_floor α c u e hα] at hdig
  set C := dStepC α c (e + 1)
  set g := dStepPartial α c u (e + 1)
  have hle : ((⌊C - g⌋ : ℤ) : ℝ) ≤ C - g := Int.floor_le _
  have hlt : C - g < (⌊C - g⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  rcases hdig with h | h <;> rw [h] at hle hlt <;> constructor <;> linarith

end Erdos482.General
