import Erdos482.General.CubicDefectLink
import Erdos482.General.CubicTorusEquidist
import Erdos482.General.EquidistDense

/-!
# Piece 2 of the cubic finish: the partial defect as a *continuous* function on `T³`

`PENDING_WORK.md ★★★` piece 2.  To feed the density tool `EquidistDense.exists_lt_of_dense_continuousAt`
we need a single function `F : T³ → ℝ` (`T = ℝ/ℤ`) with
* `F (cubicTorusOrbit W n) = cubicPartialDefect α c0 c1 c2 (⌊W·2ⁿ⌋)` — it reads the partial defect along
  the orbit, and
* `ContinuousAt F p` at any torus point `p` whose three real representatives `ρ(p i) = {·}` are nonzero
  and whose two inner `fract`-arguments are non-integers.

The representative map `ρ : ℝ/ℤ → ℝ` is the canonical interior chart `ρ x := (AddCircle.equivIco 1 0 x)`,
which satisfies `ρ (↑t) = Int.fract t` (`AddCircle.coe_equivIco_mk_apply`) and is `ContinuousAt` away from
`0` (`AddCircle.continuousAt_equivIco`).  Then `F a := cubicGpd α c0 c1 (ρ (a 0)) (ρ (a 1)) (ρ (a 2))`,
and `ContinuousAt F p` reduces (via `ContinuousAt.comp`) to `continuousAt_cubicGpd`
(`CubicDefectLink`).
-/

open Filter Topology MeasureTheory UnitAddTorus AddCircle

noncomputable section
namespace Erdos482.General

/-- The canonical real representative of a torus point: the interior chart `ℝ/ℤ → [0,1) ⊆ ℝ`. -/
def torusRep (x : AddCircle (1:ℝ)) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x : ℝ)

/-- `torusRep (↑t) = {t}`.  The representative of a coerced real is its fractional part. -/
@[simp] theorem torusRep_coe (t : ℝ) : torusRep ((t : AddCircle (1:ℝ))) = Int.fract t := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  simp only [torusRep, AddCircle.coe_equivIco_mk_apply]
  simp

/-- `torusRep` is continuous at every nonzero torus point (the chart is continuous off the cut `0`). -/
theorem continuousAt_torusRep {x : AddCircle (1:ℝ)} (hx : x ≠ 0) : ContinuousAt torusRep x := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  exact ContinuousAt.comp (g := fun y : Set.Ico (0:ℝ) (0+1) => (y : ℝ))
    (f := fun y => AddCircle.equivIco (1:ℝ) 0 y)
    continuousAt_subtype_val (AddCircle.continuousAt_equivIco (1:ℝ) 0 hx)

/-- **The partial defect as a function on `T³`.**  `F a = cubicGpd α c0 c1 (ρ (a 0)) (ρ (a 1)) (ρ (a 2))`
with `ρ = torusRep`. -/
def cubicGpdTorus (α c0 c1 : ℝ) (a : Fin 3 → AddCircle (1:ℝ)) : ℝ :=
  cubicGpd α c0 c1 (torusRep (a 0)) (torusRep (a 1)) (torusRep (a 2))

/-- **`cubicGpdTorus` reads the partial defect along the cubic orbit.**  At seed `W` and step `n`,
`F (cubicTorusOrbit W n) = cubicPartialDefect α c0 c1 c2 (⌊W·2ⁿ⌋)` (when `α = cbrt2`). -/
theorem cubicGpdTorus_orbit (c0 c1 c2 W : ℝ) (n : ℕ) :
    cubicGpdTorus cbrt2 c0 c1 (cubicTorusOrbit W n)
      = cubicPartialDefect cbrt2 c0 c1 c2 (⌊W * 2 ^ n⌋) := by
  rw [cubicPartialDefect_eq_Gpd]
  simp only [cubicGpdTorus, cubicTorusOrbit, torusRep_coe, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
  congr 1 <;> · congr 1 <;> ring

/-- **`cubicGpdTorus` is continuous at any torus point with nonzero coordinates whose two inner
`fract`-arguments are non-integers.**  The representative map `torusRep` is continuous at each nonzero
coordinate; `continuousAt_cubicGpd` supplies continuity of the algebraic core; `ContinuousAt.comp`
glues them.  This is the input `F`/`ContinuousAt F p` demanded by
`EquidistDense.exists_lt_of_dense_continuousAt`. -/
theorem continuousAt_cubicGpdTorus (α c0 c1 : ℝ) {p : Fin 3 → AddCircle (1:ℝ)}
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (h2 : p 2 ≠ 0)
    (hA : torusRep (p 1) - α * torusRep (p 0) + α * c0
            ≠ (⌊torusRep (p 1) - α * torusRep (p 0) + α * c0⌋ : ℤ))
    (hB : torusRep (p 2) - α ^ 2 * torusRep (p 0)
            - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0) + α ^ 2 * c0 + α * c1
          ≠ (⌊torusRep (p 2) - α ^ 2 * torusRep (p 0)
                - α * Int.fract (torusRep (p 1) - α * torusRep (p 0) + α * c0)
                + α ^ 2 * c0 + α * c1⌋ : ℤ)) :
    ContinuousAt (cubicGpdTorus α c0 c1) p := by
  have hΦ : ContinuousAt
      (fun a : Fin 3 → AddCircle (1:ℝ) => (torusRep (a 0), torusRep (a 1), torusRep (a 2))) p := by
    refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 3 → AddCircle (1:ℝ) => a 0)
        (continuousAt_torusRep h0) (continuous_apply 0).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 3 → AddCircle (1:ℝ) => a 1)
        (continuousAt_torusRep h1) (continuous_apply 1).continuousAt
    · exact ContinuousAt.comp (g := torusRep) (f := fun a : Fin 3 → AddCircle (1:ℝ) => a 2)
        (continuousAt_torusRep h2) (continuous_apply 2).continuousAt
  have hG : ContinuousAt (fun q : ℝ × ℝ × ℝ => cubicGpd α c0 c1 q.1 q.2.1 q.2.2)
      (torusRep (p 0), torusRep (p 1), torusRep (p 2)) :=
    continuousAt_cubicGpd α c0 c1 (torusRep (p 0), torusRep (p 1), torusRep (p 2)) hA hB
  exact ContinuousAt.comp (g := fun q : ℝ × ℝ × ℝ => cubicGpd α c0 c1 q.1 q.2.1 q.2.2)
    (f := fun a : Fin 3 → AddCircle (1:ℝ) => (torusRep (a 0), torusRep (a 1), torusRep (a 2)))
    hG hΦ

/-! ### The cubic multiplier `cbrt2` satisfies `cbrt2 ^ 3 = 2`. -/

/-- `cbrt2 ^ 3 = 2` (`cbrt2 = 2^{1/3}`). -/
theorem cbrt2_cube : cbrt2 ^ 3 = 2 := by
  rw [cbrt2, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
  norm_num

/-! ### The geometric crux: the partial defect leaves every digit window.

For any schedule `(c₀,c₁,c₂)` there is an interior, non-jump point of the canonical fractional-coordinate
cube `(0,1)³` at which the partial-defect function `cubicGpd` *leaves* the digit window `(C−2, C]`
(`C = 2c₀+α²c₁+αc₂`).  This is the width-`(α²+α) > 2` range argument made constructive: choose `(fA,fB)`
near a corner of `(0,1)²` so that `cubicGpd = α²fA + αfB` exceeds `C` (when `C < α²+α`) or falls below
`C−2` (when `C ≥ α²+α`); realize `(fA,fB)` by solving the two `fract` equations for `(r₁,r₂,r₃)`.

Disclosed as an `axiom` pending the in-flight machine proof (Aristotle job `7b1ff2ad`, "gpdwin", which
proves exactly this realization).  Once harvested/verified it discharges this statement; the entire
density contradiction below is already wired through it. -/
axiom cubicGpd_exceeds_window (c0 c1 c2 : ℝ) :
    ∃ r1 r2 r3 : ℝ, (0 < r1 ∧ r1 < 1) ∧ (0 < r2 ∧ r2 < 1) ∧ (0 < r3 ∧ r3 < 1) ∧
      (r2 - cbrt2 * r1 + cbrt2 * c0 ≠ (⌊r2 - cbrt2 * r1 + cbrt2 * c0⌋ : ℤ)) ∧
      (r3 - cbrt2 ^ 2 * r1
          - cbrt2 * Int.fract (r2 - cbrt2 * r1 + cbrt2 * c0) + cbrt2 ^ 2 * c0 + cbrt2 * c1
        ≠ (⌊r3 - cbrt2 ^ 2 * r1
              - cbrt2 * Int.fract (r2 - cbrt2 * r1 + cbrt2 * c0) + cbrt2 ^ 2 * c0 + cbrt2 * c1⌋ : ℤ)) ∧
      ((2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2) < cubicGpd cbrt2 c0 c1 r1 r2 r3 ∨
        cubicGpd cbrt2 c0 c1 r1 r2 r3 < (2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2) - 2)

/-- **Unconditional a.e.-`W` cubic impossibility.**  For `α = 2^{1/3}` and *almost every* real `W`,
no fixed 3-periodic offset schedule `(c₀,c₁,c₂)` makes the three-step cubic floor map read `W`'s base-2
digits: there is some step `n` at which the extracted digit `cubicV3(⌊W·2ⁿ⌋) − 2⌊W·2ⁿ⌋ ∉ {0,1}`.

Proof: if every digit were in `{0,1}`, then by `cubic_partial_defect_mem_window` the partial defect
`g(⌊W·2ⁿ⌋)` stays in the width-2 window `(C−2, C]` for all `n`.  But `g` along the orbit equals the
continuous-off-jumps function `cubicGpdTorus` of the dense (`ae_W_cubic_torus_orbit_dense`) torus orbit,
and `cubicGpd_exceeds_window` exhibits an interior non-jump torus point where that function *leaves* the
window.  `exists_lt_of_dense_continuousAt` (or `…gt…`) then produces an orbit step realizing the
out-of-window value — contradiction. -/
theorem ae_W_cubic_not_reads_base_two (c0 c1 c2 : ℝ) :
    ∀ᵐ W ∂(volume : Measure ℝ), ∃ n : ℕ,
      ¬ (cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 0
          ∨ cubicV3 cbrt2 c0 c1 c2 ⌊W * 2 ^ n⌋ - 2 * ⌊W * 2 ^ n⌋ = 1) := by
  haveI : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
  filter_upwards [ae_W_cubic_torus_orbit_dense] with W hdense
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ n, digitₙ = 0 ∨ digitₙ = 1`.  Window confinement of the partial defect along the orbit.
  set C : ℝ := 2 * c0 + cbrt2 ^ 2 * c1 + cbrt2 * c2 with hC
  have hwin : ∀ n : ℕ, C - 2 < cubicGpdTorus cbrt2 c0 c1 (cubicTorusOrbit W n)
      ∧ cubicGpdTorus cbrt2 c0 c1 (cubicTorusOrbit W n) ≤ C := by
    intro n
    have hw := cubic_partial_defect_mem_window cbrt2 c0 c1 c2 cbrt2_cube ⌊W * 2 ^ n⌋ (hcon n)
    rw [cubicGpdTorus_orbit (c2 := c2)]
    exact hw
  -- The interior non-jump torus point where the partial defect leaves the window.
  obtain ⟨r1, r2, r3, hr1, hr2, hr3, hA, hB, hval⟩ := cubicGpd_exceeds_window c0 c1 c2
  set P : Fin 3 → AddCircle (1:ℝ) := ![(r1 : AddCircle (1:ℝ)), (r2 : AddCircle (1:ℝ)),
    (r3 : AddCircle (1:ℝ))] with hP
  have hP0 : P 0 = (r1 : AddCircle (1:ℝ)) := rfl
  have hP1 : P 1 = (r2 : AddCircle (1:ℝ)) := rfl
  have hP2 : P 2 = (r3 : AddCircle (1:ℝ)) := rfl
  have hrep0 : torusRep (P 0) = r1 := by rw [hP0, torusRep_coe, Int.fract_eq_self.mpr ⟨hr1.1.le, hr1.2⟩]
  have hrep1 : torusRep (P 1) = r2 := by rw [hP1, torusRep_coe, Int.fract_eq_self.mpr ⟨hr2.1.le, hr2.2⟩]
  have hrep2 : torusRep (P 2) = r3 := by rw [hP2, torusRep_coe, Int.fract_eq_self.mpr ⟨hr3.1.le, hr3.2⟩]
  have hne0 : P 0 ≠ 0 := by
    rw [hP0, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr1.1.le, hr1.2⟩]; exact ne_of_gt hr1.1
  have hne1 : P 1 ≠ 0 := by
    rw [hP1, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr2.1.le, hr2.2⟩]; exact ne_of_gt hr2.1
  have hne2 : P 2 ≠ 0 := by
    rw [hP2, Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hr3.1.le, hr3.2⟩]; exact ne_of_gt hr3.1
  -- Continuity of the partial-defect function at `P`.
  have hcont : ContinuousAt (cubicGpdTorus cbrt2 c0 c1) P :=
    continuousAt_cubicGpdTorus cbrt2 c0 c1 hne0 hne1 hne2
      (by rw [hrep0, hrep1]; exact hA) (by rw [hrep0, hrep1, hrep2]; exact hB)
  -- The function value at `P` matches the real-coordinate `cubicGpd` and leaves the window.
  have hPval : cubicGpdTorus cbrt2 c0 c1 P = cubicGpd cbrt2 c0 c1 r1 r2 r3 := by
    simp only [cubicGpdTorus, hrep0, hrep1, hrep2]
  rcases hval with hgt | hlt
  · -- value `> C`: dense orbit realizes a `g > C`, contradicting `g ≤ C`.
    have hc : C < cubicGpdTorus cbrt2 c0 c1 P := by rw [hPval]; exact hgt
    obtain ⟨n, hn⟩ := exists_lt_of_dense_continuousAt hdense hcont (c := C) hc
    exact absurd (hwin n).2 (not_le.mpr hn)
  · -- value `< C − 2`: dense orbit realizes a `g < C − 2`, contradicting `C − 2 < g`.
    have hc : cubicGpdTorus cbrt2 c0 c1 P < C - 2 := by rw [hPval]; exact hlt
    obtain ⟨n, hn⟩ := exists_gt_of_dense_continuousAt hdense hcont (c := C - 2) hc
    exact absurd (hwin n).1 (not_lt.mpr hn.le)

end Erdos482.General
