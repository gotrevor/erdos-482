import Erdos482.General.St06Example

/-!
# Stoll [St06] Theorem 3.1 — subcone `𝒟₂⁻` (the cone containing Example 1.1)

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Theorem 3.1.  St06 generalizes St05 (`Thm13Closed.lean`) to a 3-parameter `(m,l,k)`
family of floor recurrences.  This module formalizes the theorem for **one subcone, `𝒟₂⁻`** — the
negative-`k` cone that contains the showcase Example 1.1 (`g=3,m=3,l=2,k=−1`, `St06Example.lean`).

Parameters (Def 2.2/2.3, subcone `𝒟₂⁻`): `g ≥ 3`, `m ≥ 1`, `0 < l ≤ g−1`, `k < 0`, and the
divisibility `(g−1) ∣ (k−1)l` (so the even closed form is integral).  Coefficients
`a = klg/((g−1)(t+mg))`, `b = g/a = (g−1)(t+mg)/(kl)`, even-step shift `l/(g−1)`.  Offset interval
(**corrected** — see `notes/ST06-THM31-ERRATUM.md`): `1 + (g−l−1)(mg+1)/(klg) ≤ ε < −(mg+1)/(kg)`.

Closed forms (`su` 0-indexed, `su n = u_{n+1}`):
* `su (2j)   = m·gʲ + ⌊t·gʲ/g⌋`        (the `u_{2n+1}` odd form, leading coeff `m`),
* `(g−1)·su (2j+1) = l(k·gʲ − 1)`       (the `u_{2n}` even form, written ×(g−1) to dodge division).

Conclusion: the Graham–Pollak difference `su(2n) − g·su(2n−2)` reads off `w`'s base-`g` digits.
Numerically verified over ~1M `(g,m,l,k,t,ε,f)` points.  Axiom-clean.
-/

namespace Erdos482.General

open Real

/-- **Even→odd inequality core (`𝒟₂⁻`).**  The two-sided bound `0 ≤ l/(g−1) + a(ε−f) < 1` that the
even→odd induction step reduces to.  `a < 0` on `𝒟₂⁻`, so the expression is increasing in `f`; the
endpoints use the corrected ε-interval.  (Same statement as `tools/aristotle/st06_d2m_eo`.) -/
theorem d2m_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  -- real casts of the integer sign facts
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlgR : (l : ℝ) ≤ (g : ℝ) - 1 := by
    have : ((l : ℤ) : ℝ) ≤ (((g : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hlg
    push_cast at this; linarith
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hkg : (k : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hklg : (k : ℝ) * (l : ℝ) * (g : ℝ) < 0 := by nlinarith
  -- clear the divisions in the ε-bounds
  have hHi : -((m : ℝ) * (g : ℝ) + 1) < ε * ((k : ℝ) * (g : ℝ)) := by
    rw [lt_div_iff_of_neg hkg] at hε_hi; exact hε_hi
  have hLo : (ε - 1) * ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) := by
    have hX : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε - 1 := by
      linarith
    rwa [div_le_iff_of_neg hklg] at hX
  -- substitute `a` and reduce both bounds to the polynomial inequalities after ×((g−1)(t+mg)) > 0
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : (0 : ℝ) < ((g : ℝ) - 1) * P := mul_pos hg1 hP
  -- key product facts feeding the two polynomial bounds
  -- (I) lower: l·P + klg·(ε−f) ≥ 0  (uses hHi scaled by l > 0, and f ≥ 0)
  -- (II) upper: l·P + klg·(ε−f) < (g−1)·P  (uses hLo, l ≤ g−1, t ≥ 1, and f < 1 strictly)
  have hlowpoly : 0 ≤ (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_lt_mul_of_pos_left hHi hlR, mul_nonneg (le_of_lt (neg_pos.mpr hklg)) hf0,
      mul_pos hlR hP, ht1, hlR]
  have hhighpoly : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) < ((g : ℝ) - 1) * P := by
    nlinarith [hLo, mul_pos (neg_pos.mpr hklg) (show (0 : ℝ) < 1 - f by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - (l : ℝ) - 1 by linarith) (show (0 : ℝ) ≤ t - 1 by linarith),
      hP]
  -- assemble: write the core as a single fraction over (g−1)P > 0
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  exact ⟨div_nonneg hlowpoly (le_of_lt hden), (div_lt_one hden).mpr hhighpoly⟩

/-- **St06 Theorem 3.1 — joint closed-form induction, subcone `𝒟₂⁻`.**  For the recurrence
`su a b ε (l/(g−1)) m` with the `𝒟₂⁻` parameters, both closed forms hold:
`su(2j) = m·gʲ + ⌊t·gʲ/g⌋` (odd form) and `(g−1)·su(2j+1) = l(k·gʲ − 1)` (even form). -/
theorem st06_thm31_d2m_closed (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ))) :
    (∀ j, su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j)
        = m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋) ∧
      (∀ j, ((g : ℤ) - 1) * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1)
        = l * (k * (g : ℤ) ^ j - 1)) := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1R : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1R
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_lt hkR
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlR
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgpos
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := ne_of_gt hP
  -- divisibility at each j:  (g−1) ∣ l·(k·gʲ − 1)
  have hdvdj : ∀ j : ℕ, ((g : ℤ) - 1) ∣ l * (k * (g : ℤ) ^ j - 1) := by
    intro j
    have h1 : ((g : ℤ) - 1) ∣ (g : ℤ) ^ j - 1 :=
      ⟨∑ i ∈ Finset.range j, (g : ℤ) ^ i, (geomSumI_mul g j).symm⟩
    have key : l * (k * (g : ℤ) ^ j - 1) = l * k * ((g : ℤ) ^ j - 1) + (k - 1) * l := by ring
    rw [key]
    exact dvd_add (Dvd.dvd.mul_left h1 (l * k)) hdvd
  -- EVEN→ODD: from the odd closed form A_j, the (a,ε) floor gives the even closed form B_j.
  have hBfromA : ∀ j, su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j)
        = m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ →
      ((g : ℤ) - 1) * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1)
        = l * (k * (g : ℤ) ^ j - 1) := by
    intro j hAj
    have hstep : su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1)
        = ⌊a * ((su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j) : ℝ) + ε)⌋ := by
      rw [su_succ, if_pos ⟨j, two_mul j⟩]
    rw [hstep, hAj]
    -- the integer Q with (g−1)·Q = l·(k·gʲ − 1)
    obtain ⟨Q, hQ⟩ := hdvdj j
    have hQr : ((g : ℝ) - 1) * (Q : ℝ) = (l : ℝ) * ((k : ℝ) * (g : ℝ) ^ j - 1) := by
      have : (((g : ℤ) - 1) * Q : ℤ) = (l * (k * (g : ℤ) ^ j - 1) : ℤ) := hQ.symm
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) this
      push_cast at h2; linarith
    set f : ℝ := t * (g : ℝ) ^ j / g - (⌊t * (g : ℝ) ^ j / g⌋ : ℝ) with hf
    have hf0 : 0 ≤ f := by rw [hf]; linarith [Int.floor_le (t * (g : ℝ) ^ j / g)]
    have hf1 : f < 1 := by rw [hf]; linarith [Int.lt_floor_add_one (t * (g : ℝ) ^ j / g)]
    have hcore := d2m_core g hg t ht1 ht2 m l k hm hl0 hlg hk a ε ha hε_lo hε_hi f hf0 hf1
    -- identity:  a·(Aⱼ + ε) − (l/(g−1) + a(ε−f)) = Q.  Prove the (g−1)-scaled version (no Q,
    -- the ε/f terms cancel), then cancel (g−1) against hQr.
    have hfe : ((⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) = t * (g : ℝ) ^ j / g - f := by rw [hf]; ring
    have hR : ((g : ℝ) - 1) * (a * (((m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) + ε)
        - ((l : ℝ) / ((g : ℝ) - 1) + a * (ε - f)))
        = (l : ℝ) * ((k : ℝ) * (g : ℝ) ^ j - 1) := by
      rw [ha]; push_cast; rw [hfe]; field_simp; ring
    have hXminus : a * (((m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) + ε)
        - ((l : ℝ) / ((g : ℝ) - 1) + a * (ε - f)) = (Q : ℝ) := by
      have hRQ := hR.trans hQr.symm
      exact mul_left_cancel₀ hg1ne hRQ
    have hfloorQ : ⌊a * (((m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) + ε)⌋ = Q := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith [hXminus, hcore.1], by linarith [hXminus, hcore.2]⟩
    rw [hfloorQ, hQ]
  -- ODD→EVEN: from the even closed form B_j, the (b, l/(g−1)) floor gives A_{j+1} (exact).
  have hAfromB : ∀ j, ((g : ℤ) - 1) * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1)
        = l * (k * (g : ℤ) ^ j - 1) →
      su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * (j + 1))
        = m * (g : ℤ) ^ (j + 1) + ⌊t * (g : ℝ) ^ (j + 1) / g⌋ := by
    intro j hBj
    have hodd : ¬ Even (2 * j + 1) := by simp [parity_simps]
    have hstep : su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * (j + 1))
        = ⌊b * ((su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1) : ℝ) + (l : ℝ) / ((g : ℝ) - 1))⌋ := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring, su_succ, if_neg hodd]
    rw [hstep]
    -- value:  b·(su(2j+1) + l/(g−1)) = m·g^{j+1} + t·gʲ  (using (g−1)·su(2j+1) = l(k·gʲ−1))
    set v : ℤ := su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1) with hv
    have hvr : ((g : ℝ) - 1) * (v : ℝ) = (l : ℝ) * ((k : ℝ) * (g : ℝ) ^ j - 1) := by
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) hBj
      push_cast at h2; linarith
    have hval : b * ((v : ℝ) + (l : ℝ) / ((g : ℝ) - 1))
        = (m : ℝ) * (g : ℝ) ^ (j + 1) + t * (g : ℝ) ^ j := by
      rw [hb]
      have hvexp : (v : ℝ) + (l : ℝ) / ((g : ℝ) - 1)
          = (l : ℝ) * (k : ℝ) * (g : ℝ) ^ j / ((g : ℝ) - 1) := by
        field_simp
        linear_combination hvr
      rw [hvexp, pow_succ]
      field_simp
      ring
    rw [hval]
    have hdig : ⌊t * (g : ℝ) ^ (j + 1) / g⌋ = ⌊t * (g : ℝ) ^ j⌋ := by
      rw [show t * (g : ℝ) ^ (j + 1) / g = t * (g : ℝ) ^ j from by rw [pow_succ]; field_simp]
    rw [hdig, show (m : ℝ) * (g : ℝ) ^ (j + 1) = (((m * (g : ℤ) ^ (j + 1) : ℤ)) : ℝ) from by push_cast; ring,
      Int.floor_intCast_add, add_comm]
  -- induction for the odd closed form A
  have hA : ∀ j, su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j)
      = m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.mul_zero, su_zero, pow_zero, mul_one]
      have hfl : ⌊t / (g : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]
        exact ⟨by positivity, by rw [div_lt_one hgpos]; linarith⟩
      rw [hfl]; omega
    | succ n ih => exact hAfromB n (hBfromA n ih)
  exact ⟨hA, fun j => hBfromA j (hA j)⟩

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₂⁻`.**  The Graham–Pollak difference of the
`𝒟₂⁻` recurrence reads off `w`'s base-`g` digit (mathlib form): for `n ≥ 1`,
`su(2n) − g·su(2n−2) = Real.digits (t·g^{n−1}/g) g 0`. -/
theorem st06_thm31_d2m_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hclosed := (st06_thm31_d2m_closed g hg t ht1 ht2 m l k hm hl0 hlg hk hdvd a b ε ha hb hε_lo hε_hi).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **Cross-check: Example 1.1 is the `𝒟₂⁻` instance `(g,m,l,k) = (3,3,2,−1)`, `t = e`, `ε = π`.**
Instantiating the general subcone theorem reproduces exactly the `e`/`π` recurrence and ternary-digit
conclusion of `st06_example11_ternary_e` — validating both the generalization and the corrected
ε-interval (`π ∈ [1, 10/3)`). -/
theorem st06_example11_from_thm31 (n : ℕ) (hn : 1 ≤ n) :
    su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * n)
        - 3 * su (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi 1 3 (2 * n - 2)
      = ((Real.digits (Real.exp 1 * (3 : ℝ) ^ (n - 1) / 3) 3 0 : ℕ) : ℤ) := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have he2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi315 : Real.pi < 3.15 := Real.pi_lt_d2
  have key := st06_thm31_d2m_digits 3 (le_refl 3) (Real.exp 1)
    (le_of_lt (Real.exp_pos 1)) (by linarith) (by exact_mod_cast he3)
    3 2 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (-3 / (Real.exp 1 + 9)) (-(Real.exp 1 + 9)) Real.pi
    (by push_cast; rw [div_eq_div_iff (by nlinarith) (by nlinarith)]; ring)
    (by push_cast; rw [eq_div_iff (by norm_num)]; ring)
    (by push_cast; norm_num; linarith)
    (by push_cast; rw [lt_div_iff_of_neg (by norm_num)]; nlinarith)
    n hn
  -- the recurrence-argument shift `↑2/(↑3−1)` is `1`
  rw [show ((2 : ℤ) : ℝ) / (((3 : ℕ) : ℝ) - 1) = 1 by norm_num] at key
  convert key using 2

end Erdos482.General
