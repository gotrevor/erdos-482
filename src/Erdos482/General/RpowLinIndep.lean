import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Int.Basic

/-!
# General degree-`d` ℤ-linear independence of `{1, 2^{1/d}, …, 2^{(d-1)/d}}`

**Context (the general-`d` self-referential frontier).**  The cubic (`CubicDefect.lean`) and quartic
(`QuarticDefect.lean`) self-referential impossibilities each needed, as their single genuinely-hard
algebraic brick, the ℤ-linear independence of the powers of `α = 2^{1/d}`:
`cubic_lin_indep_int` (`d = 3`) and `quartic_lin_indep_int` (`d = 4`).  Those were proved by *ad hoc*
per-degree arguments — a cubic elimination and an infinite 2-adic norm descent — neither of which
generalizes cleanly to arbitrary `d`.

**This file proves the brick uniformly for every `d ≥ 1`** (`rpow_lin_indep_int`): the only integer
relation `∑_{i<d} aᵢ·αⁱ = 0` is the trivial one.  The principled route is **Eisenstein at the prime
`2`**: `Xᵈ − 2` is irreducible over `ℤ` (`irreducible_of_eisenstein_criterion`), hence over `ℚ`
(Gauss's lemma, `Monic.irreducible_iff_irreducible_map_fraction_map`), so it is the minimal polynomial
of the real number `α = 2^{1/d}` over `ℚ` (`minpoly.eq_of_irreducible_of_monic`).  A nonzero rational
polynomial of degree `< d` therefore cannot vanish at `α` (`minpoly.degree_le_of_ne_zero`), which is
exactly the asserted linear independence after reading off coefficients.

This is the algebraic engine that lets the entire cubic/quartic development be replayed at any degree
`d ≥ 3` (where the partial-defect window `α + α² + … + α^{d-1}` has width `> 2`).  Mathlib's Kummer
irreducibility (`X_pow_sub_C_irreducible_of_prime`) only covers *prime* exponents, so it misses
`d = 4, 6, 8, 9, …`; Eisenstein at `2` covers **all** `d` at once.

Everything here depends only on the trust base `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos482.General

open Polynomial

/-- **General degree-`d` ℤ-linear independence of the powers of `α = 2^{1/d}`.**
For `d ≥ 1` and integers `a : Fin d → ℤ`, if `∑_{i<d} aᵢ·αⁱ = 0` (with `α = 2^{1/d}`) then every
`aᵢ = 0`.  Equivalently, `α` has degree exactly `d` over `ℚ` (minimal polynomial `Xᵈ − 2`).  This is
the per-degree algebraic obstacle generalized: `cubic_lin_indep_int`/`quartic_lin_indep_int` are the
`d = 3, 4` instances. -/
theorem rpow_lin_indep_int (d : ℕ) (hd : 1 ≤ d) (a : Fin d → ℤ)
    (h : ∑ i : Fin d, (a i : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / d)) ^ (i : ℕ) = 0) :
    ∀ i, a i = 0 := by
  set α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / d) with hα
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `α^d = 2`.
  have hαd : α ^ d = 2 := by
    rw [hα, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / d)) d,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hd0, Real.rpow_one]
  -- `Xᵈ − 2` is monic over ℤ.
  have hmonicZ : ((X : ℤ[X]) ^ d - C 2).Monic := monic_X_pow_sub_C 2 (by omega)
  -- the prime ideal `(2)` of ℤ.
  have hP : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  -- Eisenstein's criterion at `(2)`.
  have hEis : ((X : ℤ[X]) ^ d - C 2).IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
    refine ⟨?_, ?_, ?_⟩
    · -- leading coefficient `1 ∉ (2)`.
      rw [Monic.leadingCoeff hmonicZ]
      simp only [Ideal.mem_span_singleton]
      omega
    · -- every lower coefficient `∈ (2)`.
      intro n hn
      rw [natDegree_X_pow_sub_C] at hn
      have hcn : ((X : ℤ[X]) ^ d - C 2).coeff n
          = (if n = d then (1 : ℤ) else 0) - (if n = 0 then 2 else 0) := by
        simp only [coeff_sub, coeff_X_pow, coeff_C]
      rw [Ideal.mem_span_singleton, hcn, if_neg (Nat.ne_of_lt hn)]
      split_ifs <;> omega
    · -- constant coefficient `−2 ∉ (2)²`.
      have h0d : (0 : ℕ) ≠ d := by omega
      have hc0 : ((X : ℤ[X]) ^ d - C 2).coeff 0 = -2 := by
        simp [coeff_sub, coeff_X_pow, h0d]
      rw [hc0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      decide
  -- irreducible over ℤ.
  have hirrZ : Irreducible ((X : ℤ[X]) ^ d - C 2) :=
    hEis.irreducible hP hmonicZ.isPrimitive (by rw [natDegree_X_pow_sub_C]; omega)
  -- the same polynomial over ℚ is the image under `ℤ → ℚ`.
  have hmapeq : ((X : ℤ[X]) ^ d - C 2).map (algebraMap ℤ ℚ) = (X : ℚ[X]) ^ d - C 2 := by
    have h2 : (algebraMap ℤ ℚ) (2 : ℤ) = (2 : ℚ) := by norm_num
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, h2]
  -- irreducible over ℚ (Gauss's lemma for GCD domains; ℤ is a GCD monoid).
  have hirrQ : Irreducible ((X : ℚ[X]) ^ d - C 2) := by
    rw [← hmapeq]
    exact (hmonicZ.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirrZ
  -- `α` is a root of `Xᵈ − 2` over ℚ.
  have haeval : (Polynomial.aeval α) ((X : ℚ[X]) ^ d - C 2) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C]; simp [hαd]
  have hmonicQ : ((X : ℚ[X]) ^ d - C 2).Monic := monic_X_pow_sub_C 2 (by omega)
  -- hence `Xᵈ − 2` IS the minimal polynomial of `α` over ℚ; its degree is `d`.
  have hminpoly : minpoly ℚ α = (X : ℚ[X]) ^ d - C 2 :=
    (minpoly.eq_of_irreducible_of_monic hirrQ haeval hmonicQ).symm
  have hdegmp : (minpoly ℚ α).degree = (d : WithBot ℕ) := by
    rw [hminpoly, degree_X_pow_sub_C (by omega : 0 < d)]
  -- the candidate rational polynomial `∑ aᵢ Xⁱ`, degree `< d`, vanishing at `α`.
  set p : ℚ[X] := ∑ i : Fin d, C ((a i : ℚ)) * X ^ (i : ℕ) with hpdef
  have haevalp : (Polynomial.aeval α) p = 0 := by
    have hexp : (Polynomial.aeval α) p = ∑ i : Fin d, (a i : ℝ) * α ^ (i : ℕ) := by
      rw [hpdef, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [map_mul, map_pow, aeval_X, map_intCast]
    rw [hexp]; exact h
  -- a nonzero polynomial of degree `< d = deg(minpoly)` cannot vanish at `α`, so `p = 0`.
  have hp0 : p = 0 := by
    by_contra hpne
    have hle := minpoly.degree_le_of_ne_zero (A := ℚ) (x := α) hpne haevalp
    rw [hdegmp] at hle
    have hlt : p.degree < (d : WithBot ℕ) := by rw [hpdef]; exact degree_sum_fin_lt _
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  -- read off each coefficient: `aⱼ = p.coeff j = 0`.
  intro j
  have hcoeff : p.coeff (j : ℕ) = (a j : ℚ) := by
    rw [hpdef, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro i _ hij
      rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hij (Fin.val_injective hc.symm)), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ j) h'
  have : (a j : ℚ) = 0 := by rw [← hcoeff, hp0, coeff_zero]
  exact_mod_cast this

/-- **Base-`g` degree-`d` ℤ-linear independence of the powers of `α = g^{1/d}`.**
For `d ≥ 1`, a prime `p` with `p ∣ g` but `p² ∤ g` (so `Xᵈ − g` is Eisenstein at `p`), and integers
`a : Fin d → ℤ`: if `∑_{i<d} aᵢ·αⁱ = 0` (with `α = g^{1/d}`) then every `aᵢ = 0`.  Equivalently, `α`
has degree exactly `d` over `ℚ` (minimal polynomial `Xᵈ − g`).  This is the base-`g` generalization of
`rpow_lin_indep_int` (the `g = 2`, `p = 2` instance), the algebraic brick the base-`g` `Tᵈ`-orbit
equidistribution (`BaseGTorusEquidist.dXiG_ne_zero`) needs.  The Eisenstein hypothesis `p ∣ g`, `p² ∤ g`
holds whenever `g` has a prime factor of multiplicity exactly one (e.g. any squarefree `g ≥ 2`, or
`g = 6, 10, 12, …`); it covers **all** `d ≥ 1` at once. -/
theorem rpow_lin_indep_int_base (g d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : p.Prime)
    (hpg : p ∣ g) (hpg2 : ¬ (p ^ 2 ∣ g)) (a : Fin d → ℤ)
    (h : ∑ i : Fin d, (a i : ℝ) * ((g : ℝ) ^ ((1 : ℝ) / d)) ^ (i : ℕ) = 0) :
    ∀ i, a i = 0 := by
  set α : ℝ := (g : ℝ) ^ ((1 : ℝ) / d) with hα
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `α^d = g` (g ≥ 0).
  have hαd : α ^ d = (g : ℝ) := by
    rw [hα, ← Real.rpow_natCast ((g : ℝ) ^ ((1 : ℝ) / d)) d,
      ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hd0, Real.rpow_one]
  -- `Xᵈ − g` is monic over ℤ.
  have hmonicZ : ((X : ℤ[X]) ^ d - C (g : ℤ)).Monic := monic_X_pow_sub_C (g : ℤ) (by omega)
  -- `p` prime in ℤ; the prime ideal `(p)`.
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpne1 : ¬ ((p : ℤ) ∣ 1) := by
    intro hd1
    have : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hd1)
    rcases this with h1 | h1
    · have : p = 1 := by exact_mod_cast h1
      exact (Nat.Prime.one_lt hp).ne' this
    · have : (0 : ℤ) ≤ (p : ℤ) := by positivity
      omega
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  -- Eisenstein's criterion at `(p)`.
  have hEis : ((X : ℤ[X]) ^ d - C (g : ℤ)).IsEisensteinAt (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Monic.leadingCoeff hmonicZ]
      simp only [Ideal.mem_span_singleton]
      exact hpne1
    · intro n hn
      rw [natDegree_X_pow_sub_C] at hn
      have hcn : ((X : ℤ[X]) ^ d - C (g : ℤ)).coeff n
          = (if n = d then (1 : ℤ) else 0) - (if n = 0 then (g : ℤ) else 0) := by
        simp only [coeff_sub, coeff_X_pow, coeff_C]
      rw [Ideal.mem_span_singleton, hcn, if_neg (Nat.ne_of_lt hn)]
      split_ifs with hn0
      · simpa using (Int.natCast_dvd_natCast.mpr hpg)
      · simp
    · have h0d : (0 : ℕ) ≠ d := by omega
      have hc0 : ((X : ℤ[X]) ^ d - C (g : ℤ)).coeff 0 = -(g : ℤ) := by
        simp [coeff_sub, coeff_X_pow, h0d]
      rw [hc0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rw [dvd_neg, ← Int.natCast_pow, Int.natCast_dvd_natCast]
      exact hpg2
  -- irreducible over ℤ, then ℚ (Gauss).
  have hirrZ : Irreducible ((X : ℤ[X]) ^ d - C (g : ℤ)) :=
    hEis.irreducible hP hmonicZ.isPrimitive (by rw [natDegree_X_pow_sub_C]; omega)
  have hmapeq : ((X : ℤ[X]) ^ d - C (g : ℤ)).map (algebraMap ℤ ℚ) = (X : ℚ[X]) ^ d - C (g : ℚ) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    norm_num
  have hirrQ : Irreducible ((X : ℚ[X]) ^ d - C (g : ℚ)) := by
    rw [← hmapeq]
    exact (hmonicZ.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirrZ
  have haeval : (Polynomial.aeval α) ((X : ℚ[X]) ^ d - C (g : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C]; simp [hαd]
  have hmonicQ : ((X : ℚ[X]) ^ d - C (g : ℚ)).Monic := monic_X_pow_sub_C (g : ℚ) (by omega)
  have hminpoly : minpoly ℚ α = (X : ℚ[X]) ^ d - C (g : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirrQ haeval hmonicQ).symm
  have hdegmp : (minpoly ℚ α).degree = (d : WithBot ℕ) := by
    rw [hminpoly, degree_X_pow_sub_C (by omega : 0 < d)]
  set q : ℚ[X] := ∑ i : Fin d, C ((a i : ℚ)) * X ^ (i : ℕ) with hqdef
  have haevalp : (Polynomial.aeval α) q = 0 := by
    have hexp : (Polynomial.aeval α) q = ∑ i : Fin d, (a i : ℝ) * α ^ (i : ℕ) := by
      rw [hqdef, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [map_mul, map_pow, aeval_X, map_intCast]
    rw [hexp]; exact h
  have hq0 : q = 0 := by
    by_contra hqne
    have hle := minpoly.degree_le_of_ne_zero (A := ℚ) (x := α) hqne haevalp
    rw [hdegmp] at hle
    have hlt : q.degree < (d : WithBot ℕ) := by rw [hqdef]; exact degree_sum_fin_lt _
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  intro j
  have hcoeff : q.coeff (j : ℕ) = (a j : ℚ) := by
    rw [hqdef, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro i _ hij
      rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hij (Fin.val_injective hc.symm)), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ j) h'
  have : (a j : ℚ) = 0 := by rw [← hcoeff, hq0, coeff_zero]
  exact_mod_cast this

end Erdos482.General
