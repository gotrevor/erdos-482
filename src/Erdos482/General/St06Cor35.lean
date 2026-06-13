import Erdos482.General.St06Thm34
import Mathlib.NumberTheory.Rayleigh

/-!
# Stoll [St06] Corollary 3.5 — the Beatty foundation

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Corollary 3.5.  The elegant capstone unifies the binary digit-extraction recurrences
via **Beatty's / Rayleigh's theorem**: the two Beatty sequences `B⁺(1+√2)` and `B⁺(1+1/√2)` partition
the positive integers, and (extended to all signs) every `m ∈ ℤ∖{−1,0}` is `⌊r(1+1/√2)⌋` or
`⌊r(1+√2)⌋` for a unique `r`, which fixes the `w` whose binary digits the `√2`-recurrence reproduces.

This module establishes the **verified Beatty foundation** that the full corollary rests on:
* `Erdos482.General.irrational_one_add_sqrt2` — `1 + √2` is irrational;
* `Erdos482.General.holderConjugate_one_add_sqrt2` — `(1+√2)` and `(1+1/√2)` are Hölder conjugate
  (`(1+√2)⁻¹ + (1+1/√2)⁻¹ = 1`), the exact hypothesis Rayleigh's theorem needs;
* `Erdos482.General.beatty_partition_sqrt2` — Rayleigh's partition for this conjugate pair:
  `{⌊k(1+√2)⌋ | k>0} ∆ {⌊k(1+1/√2)⌋ | k>0} = ℤ_{>0}`.

The remaining step of Cor 3.5 — packaging, for each representable `m`, the `w = w(r)` and the index
shift `M = ⌊log₂ w⌋` so that `su √2 √2 (1/2) (1/2) m` reproduces `w`'s digits via the (already proved)
digit theorem — is the next increment (see `notes/ST06-PLAN.md` Cor 3.5; the per-`w` recurrence is the
`m=1,(l,k)=(0,0)` Graham–Pollak instance of `St06Thm33`).  Axiom-clean.
-/

namespace Erdos482.General

open Real
open scoped symmDiff

/-- `1 + √2` is irrational. -/
theorem irrational_one_add_sqrt2 : Irrational (1 + Real.sqrt 2) := by
  simpa using Irrational.intCast_add irrational_sqrt_two 1

/-- **The Beatty parameters of Cor 3.5 are Hölder conjugate.**  `(1+√2)⁻¹ + (1+1/√2)⁻¹ = 1`, so
Rayleigh's theorem applies to the pair `(1+√2, 1+1/√2)`. -/
theorem holderConjugate_one_add_sqrt2 :
    Real.HolderConjugate (1 + Real.sqrt 2) (1 + 1 / Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (1 : ℝ) < 1 + Real.sqrt 2 := by linarith
  rw [Real.holderConjugate_iff]
  refine ⟨h1, ?_⟩
  have hd1 : 1 + Real.sqrt 2 ≠ 0 := by positivity
  have hd2 : 1 + 1 / Real.sqrt 2 ≠ 0 := by positivity
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [h2, hpos]

/-- **Rayleigh's theorem for the Cor 3.5 pair.**  The Beatty sequences of `1+√2` and `1+1/√2`
partition the positive integers:  `B⁺(1+√2) ∆ B⁺(1+1/√2) = ℤ_{>0}`. -/
theorem beatty_partition_sqrt2 :
    {beattySeq (1 + Real.sqrt 2) k | k > 0}
      ∆ {beattySeq (1 + 1 / Real.sqrt 2) k | k > 0} = {n | 0 < n} :=
  irrational_one_add_sqrt2.beattySeq_symmDiff_beattySeq_pos holderConjugate_one_add_sqrt2

end Erdos482.General
