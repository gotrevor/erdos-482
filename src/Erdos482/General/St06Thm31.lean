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

/-- **St06 Theorem 3.1 — joint closed-form induction, cone-agnostic master.**  The induction skeleton
shared by all six subcones: it takes the even→odd inequality core as an abstract hypothesis `hcore`
(`0 ≤ l/(g−1)+a(ε−f) < 1` for every fractional part `f ∈ [0,1)`), so each subcone reduces to supplying
its own verified ε-interval core.  Requires only `l ≠ 0`, `k ≠ 0`, `t+mg ≠ 0`, the divisibility
`(g−1)∣(k−1)l`, and `a,b` of the St06 form.  Both closed forms follow:
`su(2j) = m·gʲ + ⌊t·gʲ/g⌋` and `(g−1)·su(2j+1) = l(k·gʲ − 1)`. -/
theorem st06_thm31_closed_core (g : ℕ) (hg : 2 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hlne0 : l ≠ 0) (hkne0 : k ≠ 0) (hPne0 : t + (m : ℝ) * (g : ℝ) ≠ 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hcore : ∀ f : ℝ, 0 ≤ f → f < 1 →
      0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
        (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1) :
    (∀ j, su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j)
        = m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋) ∧
      (∀ j, ((g : ℤ) - 1) * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1)
        = l * (k * (g : ℤ) ^ j - 1)) := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1R : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1R
  have hlne : (l : ℝ) ≠ 0 := by exact_mod_cast hlne0
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hkne0
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgpos
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := hPne0
  have hPne2 : (g : ℝ) * (m : ℝ) + t ≠ 0 := by
    rw [show (g : ℝ) * (m : ℝ) + t = t + (m : ℝ) * (g : ℝ) by ring]; exact hPne
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
    have hcoref := hcore f hf0 hf1
    -- identity:  a·(Aⱼ + ε) − (l/(g−1) + a(ε−f)) = Q.  Prove the (g−1)-scaled version (no Q,
    -- the ε/f terms cancel), then cancel (g−1) against hQr.
    have hfe : ((⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) = t * (g : ℝ) ^ j / g - f := by rw [hf]; ring
    have hR : ((g : ℝ) - 1) * (a * (((m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) + ε)
        - ((l : ℝ) / ((g : ℝ) - 1) + a * (ε - f)))
        = (l : ℝ) * ((k : ℝ) * (g : ℝ) ^ j - 1) := by
      rw [ha]; push_cast; rw [hfe]
      rw [show t + (m : ℝ) * (g : ℝ) = (g : ℝ) * (m : ℝ) + t from by ring]
      field_simp
      ring
    have hXminus : a * (((m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) + ε)
        - ((l : ℝ) / ((g : ℝ) - 1) + a * (ε - f)) = (Q : ℝ) := by
      have hRQ := hR.trans hQr.symm
      exact mul_left_cancel₀ hg1ne hRQ
    have hfloorQ : ⌊a * (((m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋ : ℤ) : ℝ) + ε)⌋ = Q := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith [hXminus, hcoref.1], by linarith [hXminus, hcoref.2]⟩
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

/-- **St06 Theorem 3.1 — joint closed-form induction, subcone `𝒟₂⁻`** (`k < 0`).  Master + `d2m_core`. -/
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
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    positivity
  exact st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_lt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d2m_core g hg t ht1 ht2 m l k hm hl0 hlg hk a ε ha hε_lo hε_hi f hf0 hf1)

/-- **Even→odd inequality core (`𝒟₂⁺`, `k > 0`).**  Mirror of `d2m_core`: now `a > 0` so the core
is decreasing in `f`; the corrected `𝒟₂⁺` ε-interval is `1 − (mg+1)/(kg) ≤ ε < (g−l−1)(mg+1)/(klg)`
(again no spurious `+1` on the open endpoint — `notes/ST06-THM31-ERRATUM.md`).  Verified over ~390k
points. -/
theorem d2p_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : 0 < k)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlgR : (l : ℝ) ≤ (g : ℝ) - 1 := by
    have : ((l : ℤ) : ℝ) ≤ (((g : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hlg
    push_cast at this; linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hkg : (0 : ℝ) < (k : ℝ) * (g : ℝ) := by positivity
  have hklg : (0 : ℝ) < (k : ℝ) * (l : ℝ) * (g : ℝ) := by positivity
  -- clear the divisions in the ε-bounds
  have hLo : -((m : ℝ) * (g : ℝ) + 1) ≤ (ε - 1) * ((k : ℝ) * (g : ℝ)) := by
    have hX : -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε - 1 := by
      rw [neg_div]; linarith
    rwa [div_le_iff₀ hkg] at hX
  have hHi : ε * ((k : ℝ) * (l : ℝ) * (g : ℝ)) < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) := by
    rw [lt_div_iff₀ hklg] at hε_hi; exact hε_hi
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : (0 : ℝ) < ((g : ℝ) - 1) * P := mul_pos hg1 hP
  have hlowpoly : 0 ≤ (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_le_mul_of_nonneg_left hLo (le_of_lt hlR), mul_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_pos hlR hP, ht1, hlR]
  have hhighpoly : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) < ((g : ℝ) - 1) * P := by
    nlinarith [hHi, mul_nonneg (le_of_lt hklg) hf0,
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - (l : ℝ) - 1 by linarith) (show (0 : ℝ) ≤ t - 1 by linarith), hP]
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  exact ⟨div_nonneg hlowpoly (le_of_lt hden), (div_lt_one hden).mpr hhighpoly⟩

/-- **St06 Theorem 3.1 — joint closed-form induction, subcone `𝒟₂⁺`** (`k > 0`).  Master + `d2p_core`. -/
theorem st06_thm31_d2p_closed (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ))) :
    (∀ j, su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j)
        = m * (g : ℤ) ^ j + ⌊t * (g : ℝ) ^ j / g⌋) ∧
      (∀ j, ((g : ℤ) - 1) * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * j + 1)
        = l * (k * (g : ℤ) ^ j - 1)) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    positivity
  exact st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_gt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d2p_core g hg t ht1 ht2 m l k hm hl0 hlg hk a ε ha hε_lo hε_hi f hf0 hf1)

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₂⁺`.** -/
theorem st06_thm31_d2p_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hclosed := (st06_thm31_d2p_closed g hg t ht1 ht2 m l k hm hl0 hlg hk hdvd a b ε ha hb hε_lo hε_hi).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

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
  -- v4.31's `convert` over-splits the `(3:ℝ)`-vs-`↑3` coercion into extra goals; close them
  convert key using 2 <;> first | rfl | norm_num | push_cast

/-! ## Subcone `𝒟₁` (cone `𝒜₁`: `l < 0`) — shows the master handles negative `l` -/

/-- **Even→odd inequality core (`𝒟₁⁻`, `k < 0`, `l < 0`).**  Here `kl > 0` so `a > 0`.  Corrected
`𝒟₁⁻` ε-interval `1 − (m+1)/k ≤ ε < (g−l−1)(mg+1)/(klg)` (verified ~160k points). -/
theorem d1m_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : l < 0) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (l : ℝ) < 0 := by exact_mod_cast hl
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hlg_neg : (l : ℝ) * (g : ℝ) < 0 := mul_neg_of_neg_of_pos hlR hgpos
  have hklg : (0 : ℝ) < (k : ℝ) * (l : ℝ) * (g : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) * (l : ℝ) := mul_pos_of_neg_of_neg hkR hlR
    positivity
  -- clear the divisions in the ε-bounds
  have hLo : (ε - 1) * (k : ℝ) ≤ -((m : ℝ) + 1) := by
    have h1 : -((m : ℝ) + 1) / (k : ℝ) ≤ ε - 1 := by rw [neg_div]; linarith
    rwa [div_le_iff_of_neg hkR] at h1
  have hHi : ε * ((k : ℝ) * (l : ℝ) * (g : ℝ)) < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) := by
    rw [lt_div_iff₀ hklg] at hε_hi; exact hε_hi
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : (0 : ℝ) < ((g : ℝ) - 1) * P := mul_pos hg1 hP
  have hlowpoly : 0 ≤ (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    -- klg(ε−f) ≥ klg(ε−1) ≥ −(m+1)·l·g ;  l·P − (m+1)·l·g = l·(t−g) ≥ 0
    nlinarith [mul_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_le_mul_of_nonpos_right hLo (le_of_lt hlg_neg),
      mul_nonneg (le_of_lt (neg_pos.mpr hlR)) (le_of_lt (show (0 : ℝ) < (g : ℝ) - t by linarith))]
  have hhighpoly : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) < ((g : ℝ) - 1) * P := by
    nlinarith [hHi, mul_nonneg (le_of_lt hklg) hf0,
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - (l : ℝ) - 1 by linarith) (show (0 : ℝ) ≤ t - 1 by linarith), hP]
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  exact ⟨div_nonneg hlowpoly (le_of_lt hden), (div_lt_one hden).mpr hhighpoly⟩

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₁⁻`** (`k<0`, `l<0`).  Master + `d1m_core`. -/
theorem st06_thm31_d1m_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : l < 0) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    positivity
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_lt hl) (ne_of_lt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d1m_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-! ## Subcone `𝒟₃` (cone `𝒜₃`: `l > g−1`) -/

/-- **Even→odd inequality core (`𝒟₃⁻`, `k < 0`, `l > g−1`).**  `kl < 0` so `a < 0`.  Corrected `𝒟₃⁻`
ε-interval `1 + (g−l−1)(m+1)/(kl) ≤ ε < −(mg+1)/(kg)`.  The upper-bound algebra uses `(g−1−l)(g−t) < 0`
(here `g−1−l < 0` since `l > g−1`). -/
theorem d3m_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : (g : ℤ) - 1 < l) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (g : ℝ) - 1 < (l : ℝ) := by
    have : (((g : ℤ) - 1 : ℤ) : ℝ) < ((l : ℤ) : ℝ) := by exact_mod_cast hl
    push_cast at this; linarith
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hkg : (k : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkl : (k : ℝ) * (l : ℝ) < 0 := mul_neg_of_neg_of_pos hkR hl0
  have hklg : (k : ℝ) * (l : ℝ) * (g : ℝ) < 0 := by nlinarith
  -- clear the divisions in the ε-bounds
  have hHi : -((m : ℝ) * (g : ℝ) + 1) < ε * ((k : ℝ) * (g : ℝ)) := by
    rw [lt_div_iff_of_neg hkg] at hε_hi; exact hε_hi
  have hLo : (ε - 1) * ((k : ℝ) * (l : ℝ)) ≤ ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) := by
    have hX : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε - 1 := by linarith
    rwa [div_le_iff_of_neg hkl] at hX
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : (0 : ℝ) < ((g : ℝ) - 1) * P := mul_pos hg1 hP
  have hlowpoly : 0 ≤ (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_lt_mul_of_pos_left hHi hl0, mul_nonneg (le_of_lt (neg_pos.mpr hklg)) hf0,
      mul_pos hl0 hP, ht1, hl0]
  have hhighpoly : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) < ((g : ℝ) - 1) * P := by
    nlinarith [mul_le_mul_of_nonneg_left hLo (le_of_lt hgpos), mul_neg_of_neg_of_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_pos (show (0 : ℝ) < (l : ℝ) - ((g : ℝ) - 1) by linarith) (show (0 : ℝ) < (g : ℝ) - t by linarith), hP]
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  exact ⟨div_nonneg hlowpoly (le_of_lt hden), (div_lt_one hden).mpr hhighpoly⟩

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₃⁻`** (`k<0`, `l>g−1`).  Master + `d3m_core`. -/
theorem st06_thm31_d3m_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : (g : ℤ) - 1 < l) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hl0 : 0 < l := by
    have hgz : (3 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
    omega
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    positivity
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_lt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d3m_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **Even→odd inequality core (`𝒟₃⁺`, `k > 0`, `l > g−1`).**  `kl > 0` so `a > 0`.  Corrected `𝒟₃⁺`
ε-interval `1 − (mg+1)/(kg) ≤ ε < (g−l−1)(m+1)/(kl)`. -/
theorem d3p_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : (g : ℤ) - 1 < l) (hk : 0 < k)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (g : ℝ) - 1 < (l : ℝ) := by
    have : (((g : ℤ) - 1 : ℤ) : ℝ) < ((l : ℤ) : ℝ) := by exact_mod_cast hl
    push_cast at this; linarith
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hkg : (0 : ℝ) < (k : ℝ) * (g : ℝ) := by positivity
  have hkl : (0 : ℝ) < (k : ℝ) * (l : ℝ) := by positivity
  have hklg : (0 : ℝ) < (k : ℝ) * (l : ℝ) * (g : ℝ) := by positivity
  have hLo : -((m : ℝ) * (g : ℝ) + 1) ≤ (ε - 1) * ((k : ℝ) * (g : ℝ)) := by
    have hX : -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε - 1 := by rw [neg_div]; linarith
    rwa [div_le_iff₀ hkg] at hX
  have hHi : ε * ((k : ℝ) * (l : ℝ)) < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) := by
    rw [lt_div_iff₀ hkl] at hε_hi; exact hε_hi
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : (0 : ℝ) < ((g : ℝ) - 1) * P := mul_pos hg1 hP
  have hlowpoly : 0 ≤ (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_le_mul_of_nonneg_left hLo (le_of_lt hl0), mul_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_pos hl0 hP, ht1, hl0]
  have hhighpoly : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) < ((g : ℝ) - 1) * P := by
    nlinarith [mul_lt_mul_of_pos_left hHi hgpos, mul_nonneg (le_of_lt hklg) hf0,
      mul_pos (show (0 : ℝ) < (l : ℝ) - ((g : ℝ) - 1) by linarith) (show (0 : ℝ) < (g : ℝ) - t by linarith), hP]
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  exact ⟨div_nonneg hlowpoly (le_of_lt hden), (div_lt_one hden).mpr hhighpoly⟩

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₃⁺`** (`k>0`, `l>g−1`).  Master + `d3p_core`. -/
theorem st06_thm31_d3p_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : (g : ℤ) - 1 < l) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hl0 : 0 < l := by
    have hgz : (3 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
    omega
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    positivity
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_gt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d3p_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **Even→odd inequality core (`𝒟₁⁺`, `k > 0`, `l < 0`).**  `kl < 0` so `a < 0`.  Corrected `𝒟₁⁺`
ε-interval `1 + (g−l−1)(mg+1)/(klg) ≤ ε < −(m+1)/k`.  Completes the `𝒜₁` (and hence `Ω₁`) cones. -/
theorem d1p_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : l < 0) (hk : 0 < k)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) + 1) / (k : ℝ))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlR : (l : ℝ) < 0 := by exact_mod_cast hl
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : (0 : ℝ) < t + (m : ℝ) * (g : ℝ) := by nlinarith
  have hlg_neg : (l : ℝ) * (g : ℝ) < 0 := mul_neg_of_neg_of_pos hlR hgpos
  have hklg : (k : ℝ) * (l : ℝ) * (g : ℝ) < 0 := by
    have : (k : ℝ) * (l : ℝ) < 0 := mul_neg_of_pos_of_neg hkR hlR
    nlinarith
  have hHi : ε * (k : ℝ) < -((m : ℝ) + 1) := by
    rw [lt_div_iff₀ hkR] at hε_hi; exact hε_hi
  have hLo : (ε - 1) * ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) := by
    have hX : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε - 1 := by
      linarith
    rwa [div_le_iff_of_neg hklg] at hX
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : (0 : ℝ) < ((g : ℝ) - 1) * P := mul_pos hg1 hP
  have hlowpoly : 0 ≤ (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_lt_mul_of_neg_right hHi hlg_neg, mul_nonneg (le_of_lt (neg_pos.mpr hklg)) hf0,
      mul_pos (neg_pos.mpr hlR) (show (0 : ℝ) < (g : ℝ) - t by linarith), hP, hmR]
  have hhighpoly : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) < ((g : ℝ) - 1) * P := by
    nlinarith [hLo, mul_neg_of_neg_of_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 1 - (l : ℝ) by linarith) (show (0 : ℝ) ≤ t - 1 by linarith), hP]
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  exact ⟨div_nonneg hlowpoly (le_of_lt hden), (div_lt_one hden).mpr hhighpoly⟩

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₁⁺`** (`k>0`, `l<0`).  Master + `d1p_core`. -/
theorem st06_thm31_d1p_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : 1 ≤ m) (hl : l < 0) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) + 1) / (k : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    positivity
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_lt hl) (ne_of_gt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d1p_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-! ## Cone `Ω₂` (`m ≤ −2`): here `P = t+mg < 0`, so `(g−1)P < 0` and the final `÷(g−1)P` step flips.
The cone-agnostic master `st06_thm31_closed_core` is UNCHANGED (it only needs `t+mg ≠ 0`); only the
`*_core` inequality lemmas need the sign-flipped division.  `𝒟₅⁻` below is the template. -/

/-- **Even→odd inequality core (`𝒟₅⁻`, `Ω₂`: `m ≤ −2`, `0 < l ≤ g−1`, `k < 0`).**  `P = t+mg < 0`,
`klg < 0`, so `a > 0`.  Corrected `𝒟₅⁻` ε-interval `1 − (m+1)/k ≤ ε < (g−l−1)(m+1)/(kl)` (verified
~37k pts).  Numerator/denominator are both `≤ 0`, so `core = N/((g−1)P) ≥ 0` via the negative-denominator
division lemmas. -/
theorem d5m_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlgR : (l : ℝ) ≤ (g : ℝ) - 1 := by
    have : ((l : ℤ) : ℝ) ≤ (((g : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hlg
    push_cast at this; linarith
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkl : (k : ℝ) * (l : ℝ) < 0 := mul_neg_of_neg_of_pos hkR hlR
  have hklg : (k : ℝ) * (l : ℝ) * (g : ℝ) < 0 := by nlinarith
  -- clear the divisions in the ε-bounds
  have hLo : (ε - 1) * (k : ℝ) ≤ -((m : ℝ) + 1) := by
    have h1 : -((m : ℝ) + 1) / (k : ℝ) ≤ ε - 1 := by rw [neg_div]; linarith
    rwa [div_le_iff_of_neg hkR] at h1
  have hHi : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) < ε * ((k : ℝ) * (l : ℝ)) := by
    rw [lt_div_iff_of_neg hkl] at hε_hi; exact hε_hi
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : ((g : ℝ) - 1) * P < 0 := mul_neg_of_pos_of_neg hg1 hP
  -- (I')  N ≤ 0   (N := l·P + klg(ε−f))
  have hNle : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hLo (show (0 : ℝ) ≤ (l : ℝ) * (g : ℝ) by positivity),
      mul_neg_of_neg_of_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_pos hlR (show (0 : ℝ) < (g : ℝ) - t by linarith)]
  -- (II')  N > (g−1)·P
  have hNgt : ((g : ℝ) - 1) * P < (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_lt_mul_of_pos_left hHi hgpos, mul_nonneg (le_of_lt (neg_pos.mpr hklg)) hf0,
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 1 - (l : ℝ) by linarith) (show (0 : ℝ) ≤ (g : ℝ) - t by linarith), hP]
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
  have hPne0 : P ≠ 0 := ne_of_lt hP
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  refine ⟨?_, (div_lt_one_of_neg hden).mpr hNgt⟩
  rw [← neg_div_neg_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₅⁻`** (`Ω₂`: `m≤−2`, `0<l≤g−1`, `k<0`).
Master + `d5m_core`; the first `Ω₂` cone. -/
theorem st06_thm31_d5m_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
    linarith
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_lt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d5m_core g hg t ht1 ht2 m l k hm hl0 hlg hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **Even→odd inequality core (`𝒟₅⁺`, `Ω₂`: `m ≤ −2`, `0 < l ≤ g−1`, `k > 0`).**  `P < 0`, `klg > 0`,
so `a < 0` — the second `Ω₂` template (a<0/P<0).  Corrected ε-interval
`1 + (g−l−1)(m+1)/(kl) ≤ ε < −(m+1)/k`. -/
theorem d5p_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : 0 < k)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) + 1) / (k : ℝ))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlgR : (l : ℝ) ≤ (g : ℝ) - 1 := by
    have : ((l : ℤ) : ℝ) ≤ (((g : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hlg
    push_cast at this; linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkl : (0 : ℝ) < (k : ℝ) * (l : ℝ) := by positivity
  have hklg : (0 : ℝ) < (k : ℝ) * (l : ℝ) * (g : ℝ) := by positivity
  have hHi : ε * (k : ℝ) < -((m : ℝ) + 1) := by
    rw [lt_div_iff₀ hkR] at hε_hi; exact hε_hi
  have hLo : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) ≤ (ε - 1) * ((k : ℝ) * (l : ℝ)) := by
    have hX : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε - 1 := by linarith
    rwa [div_le_iff₀ hkl] at hX
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : ((g : ℝ) - 1) * P < 0 := mul_neg_of_pos_of_neg hg1 hP
  have hNle : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) ≤ 0 := by
    nlinarith [mul_lt_mul_of_pos_right hHi (show (0 : ℝ) < (l : ℝ) * (g : ℝ) by positivity),
      mul_nonneg (le_of_lt hklg) hf0, mul_pos hlR (show (0 : ℝ) < (g : ℝ) - t by linarith)]
  have hNgt : ((g : ℝ) - 1) * P < (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_le_mul_of_nonneg_left hLo (le_of_lt hgpos), mul_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 1 - (l : ℝ) by linarith) (show (0 : ℝ) ≤ (g : ℝ) - t by linarith), hP]
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
  have hPne0 : P ≠ 0 := ne_of_lt hP
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  refine ⟨?_, (div_lt_one_of_neg hden).mpr hNgt⟩
  rw [← neg_div_neg_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₅⁺`** (`Ω₂`: `m≤−2`, `0<l≤g−1`, `k>0`).
Master + `d5p_core`. -/
theorem st06_thm31_d5p_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl0 : 0 < l) (hlg : l ≤ (g : ℤ) - 1) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) + 1) / (k : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
    linarith
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_gt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d5p_core g hg t ht1 ht2 m l k hm hl0 hlg hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **Even→odd core (`𝒟₄⁺`, `Ω₂`: `m≤−2`, `l<0`, `k>0`).**  `a > 0` (d5m-template).  Interval
`1 − (mg+1)/(kg) ≤ ε < (g−l−1)(m+1)/(kl)`. -/
theorem d4p_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : l < 0) (hk : 0 < k)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hlR : (l : ℝ) < 0 := by exact_mod_cast hl
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkg : (0 : ℝ) < (k : ℝ) * (g : ℝ) := by positivity
  have hkl : (k : ℝ) * (l : ℝ) < 0 := mul_neg_of_pos_of_neg hkR hlR
  have hklg : (k : ℝ) * (l : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hLo : -((m : ℝ) * (g : ℝ) + 1) ≤ (ε - 1) * ((k : ℝ) * (g : ℝ)) := by
    have hX : -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε - 1 := by rw [neg_div]; linarith
    rwa [div_le_iff₀ hkg] at hX
  have hHi : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) < ε * ((k : ℝ) * (l : ℝ)) := by
    rw [lt_div_iff_of_neg hkl] at hε_hi; exact hε_hi
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : ((g : ℝ) - 1) * P < 0 := mul_neg_of_pos_of_neg hg1 hP
  have hNle : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonpos_right hLo (le_of_lt hlR), mul_neg_of_neg_of_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_nonneg (neg_pos.mpr hlR).le (show (0 : ℝ) ≤ t - 1 by linarith)]
  have hNgt : ((g : ℝ) - 1) * P < (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_lt_mul_of_pos_left hHi hgpos, mul_nonneg (neg_pos.mpr hklg).le hf0,
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 1 - (l : ℝ) by linarith) (show (0 : ℝ) ≤ (g : ℝ) - t by linarith), hP]
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
  have hPne0 : P ≠ 0 := ne_of_lt hP
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  refine ⟨?_, (div_lt_one_of_neg hden).mpr hNgt⟩
  rw [← neg_div_neg_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **Even→odd core (`𝒟₄⁻`, `Ω₂`: `m≤−2`, `l<0`, `k<0`).**  `a < 0` (d5p-template).  Interval
`1 + (g−l−1)(m+1)/(kl) ≤ ε < −(mg+1)/(kg)`. -/
theorem d4m_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : l < 0) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hlR : (l : ℝ) < 0 := by exact_mod_cast hl
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkg : (k : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkl : (0 : ℝ) < (k : ℝ) * (l : ℝ) := mul_pos_of_neg_of_neg hkR hlR
  have hklg : (0 : ℝ) < (k : ℝ) * (l : ℝ) * (g : ℝ) := by positivity
  have hHi : -((m : ℝ) * (g : ℝ) + 1) < ε * ((k : ℝ) * (g : ℝ)) := by
    rw [lt_div_iff_of_neg hkg] at hε_hi; exact hε_hi
  have hLo : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) ≤ (ε - 1) * ((k : ℝ) * (l : ℝ)) := by
    have hX : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε - 1 := by linarith
    rwa [div_le_iff₀ hkl] at hX
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : ((g : ℝ) - 1) * P < 0 := mul_neg_of_pos_of_neg hg1 hP
  have hNle : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) ≤ 0 := by
    nlinarith [mul_lt_mul_of_neg_right hHi hlR, mul_nonneg (le_of_lt hklg) hf0,
      mul_nonneg (neg_pos.mpr hlR).le (show (0 : ℝ) ≤ t - 1 by linarith)]
  have hNgt : ((g : ℝ) - 1) * P < (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [mul_le_mul_of_nonneg_left hLo (le_of_lt hgpos), mul_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) - 1 - (l : ℝ) by linarith) (show (0 : ℝ) ≤ (g : ℝ) - t by linarith), hP]
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
  have hPne0 : P ≠ 0 := ne_of_lt hP
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  refine ⟨?_, (div_lt_one_of_neg hden).mpr hNgt⟩
  rw [← neg_div_neg_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₄⁺`** (`Ω₂`: `m≤−2`, `l<0`, `k>0`). -/
theorem st06_thm31_d4p_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : l < 0) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
    linarith
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_lt hl) (ne_of_gt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d4p_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₄⁻`** (`Ω₂`: `m≤−2`, `l<0`, `k<0`). -/
theorem st06_thm31_d4m_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : l < 0) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) + 1) / ((k : ℝ) * (l : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (g : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
    linarith
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_lt hl) (ne_of_lt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d4m_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **Even→odd core (`𝒟₆⁻`, `Ω₂`: `m≤−2`, `l>g−1`, `k<0`).**  `a > 0` (d5m-template).  Interval
`1 − (m+1)/k ≤ ε < (g−l−1)(mg+1)/(klg)`. -/
theorem d6m_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : (g : ℤ) - 1 < l) (hk : k < 0)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hlR : (g : ℝ) - 1 < (l : ℝ) := by
    have : (((g : ℤ) - 1 : ℤ) : ℝ) < ((l : ℤ) : ℝ) := by exact_mod_cast hl
    push_cast at this; linarith
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkl : (k : ℝ) * (l : ℝ) < 0 := mul_neg_of_neg_of_pos hkR hl0
  have hklg : (k : ℝ) * (l : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hLo : (ε - 1) * (k : ℝ) ≤ -((m : ℝ) + 1) := by
    have h1 : -((m : ℝ) + 1) / (k : ℝ) ≤ ε - 1 := by rw [neg_div]; linarith
    rwa [div_le_iff_of_neg hkR] at h1
  have hHi : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) < ε * ((k : ℝ) * (l : ℝ) * (g : ℝ)) := by
    rw [lt_div_iff_of_neg hklg] at hε_hi; exact hε_hi
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : ((g : ℝ) - 1) * P < 0 := mul_neg_of_pos_of_neg hg1 hP
  have hNle : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hLo (show (0 : ℝ) ≤ (l : ℝ) * (g : ℝ) by positivity),
      mul_neg_of_neg_of_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_pos hl0 (show (0 : ℝ) < (g : ℝ) - t by linarith)]
  have hNgt : ((g : ℝ) - 1) * P < (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [hHi, mul_nonneg (neg_pos.mpr hklg).le hf0,
      mul_nonneg (show (0 : ℝ) ≤ (l : ℝ) - ((g : ℝ) - 1) by linarith) (show (0 : ℝ) ≤ t - 1 by linarith), hP]
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
  have hPne0 : P ≠ 0 := ne_of_lt hP
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  refine ⟨?_, (div_lt_one_of_neg hden).mpr hNgt⟩
  rw [← neg_div_neg_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **Even→odd core (`𝒟₆⁺`, `Ω₂`: `m≤−2`, `l>g−1`, `k>0`).**  `a < 0` (d5p-template).  Interval
`1 + (g−l−1)(mg+1)/(klg) ≤ ε < −(m+1)/k`. -/
theorem d6p_core (g : ℕ) (hg : 3 ≤ g) (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : (g : ℤ) - 1 < l) (hk : 0 < k)
    (a ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) + 1) / (k : ℝ))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 ≤ (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) ∧
      (l : ℝ) / ((g : ℝ) - 1) + a * (ε - f) < 1 := by
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hlR : (g : ℝ) - 1 < (l : ℝ) := by
    have : (((g : ℤ) - 1 : ℤ) : ℝ) < ((l : ℤ) : ℝ) := by exact_mod_cast hl
    push_cast at this; linarith
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hP : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
  have hkl : (0 : ℝ) < (k : ℝ) * (l : ℝ) := by positivity
  have hklg : (0 : ℝ) < (k : ℝ) * (l : ℝ) * (g : ℝ) := by positivity
  have hHi : ε * (k : ℝ) < -((m : ℝ) + 1) := by
    rw [lt_div_iff₀ hkR] at hε_hi; exact hε_hi
  have hLo : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) ≤ (ε - 1) * ((k : ℝ) * (l : ℝ) * (g : ℝ)) := by
    have hX : ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε - 1 := by
      linarith
    rwa [div_le_iff₀ hklg] at hX
  subst ha
  set P : ℝ := t + (m : ℝ) * (g : ℝ) with hPdef
  have hden : ((g : ℝ) - 1) * P < 0 := mul_neg_of_pos_of_neg hg1 hP
  have hNle : (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) ≤ 0 := by
    nlinarith [mul_lt_mul_of_pos_right hHi (show (0 : ℝ) < (l : ℝ) * (g : ℝ) by positivity),
      mul_nonneg (le_of_lt hklg) hf0, mul_pos hl0 (show (0 : ℝ) < (g : ℝ) - t by linarith)]
  have hNgt : ((g : ℝ) - 1) * P < (l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f) := by
    nlinarith [hLo, mul_pos hklg (show (0 : ℝ) < 1 - f by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (l : ℝ) - ((g : ℝ) - 1) by linarith) (show (0 : ℝ) ≤ t - 1 by linarith), hP]
  have hg1ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt hg1
  have hPne0 : P ≠ 0 := ne_of_lt hP
  have hfrac : (l : ℝ) / ((g : ℝ) - 1)
      + ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * P) * (ε - f)
      = ((l : ℝ) * P + ((k : ℝ) * (l : ℝ) * (g : ℝ)) * (ε - f)) / (((g : ℝ) - 1) * P) := by
    field_simp
  rw [hfrac]
  refine ⟨?_, (div_lt_one_of_neg hden).mpr hNgt⟩
  rw [← neg_div_neg_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₆⁻`** (`Ω₂`: `m≤−2`, `l>g−1`, `k<0`). -/
theorem st06_thm31_d6m_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : (g : ℤ) - 1 < l) (hk : k < 0)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 - ((m : ℝ) + 1) / (k : ℝ) ≤ ε)
    (hε_hi : ε < ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hl0 : 0 < l := by
    have hgz : (3 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
    omega
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
    linarith
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_lt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d6m_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

/-- **St06 Theorem 3.1 — digit extraction, subcone `𝒟₆⁺`** (`Ω₂`: `m≤−2`, `l>g−1`, `k>0`). -/
theorem st06_thm31_d6p_digits (g : ℕ) [NeZero g] (hg : 3 ≤ g) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : 1 ≤ t) (ht2 : t < (g : ℝ))
    (m l k : ℤ) (hm : m ≤ -2) (hl : (g : ℤ) - 1 < l) (hk : 0 < k)
    (hdvd : ((g : ℤ) - 1) ∣ (k - 1) * l)
    (a b ε : ℝ)
    (ha : a = ((k : ℝ) * (l : ℝ) * (g : ℝ)) / (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))))
    (hb : b = (((g : ℝ) - 1) * (t + (m : ℝ) * (g : ℝ))) / ((k : ℝ) * (l : ℝ)))
    (hε_lo : 1 + ((g : ℝ) - (l : ℝ) - 1) * ((m : ℝ) * (g : ℝ) + 1) / ((k : ℝ) * (l : ℝ) * (g : ℝ)) ≤ ε)
    (hε_hi : ε < -((m : ℝ) + 1) / (k : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n)
        - g * su a b ε ((l : ℝ) / ((g : ℝ) - 1)) m (2 * n - 2)
      = ((Real.digits (t * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) : ℤ) := by
  have hl0 : 0 < l := by
    have hgz : (3 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
    omega
  have hPne : t + (m : ℝ) * (g : ℝ) ≠ 0 := by
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
    have hg3 : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have : t + (m : ℝ) * (g : ℝ) < 0 := by nlinarith
    linarith
  have hclosed := (st06_thm31_closed_core g (by omega) t ht1 ht2 m l k (ne_of_gt hl0) (ne_of_gt hk) hPne
    hdvd a b ε ha hb (fun f hf0 hf1 => d6p_core g hg t ht1 ht2 m l k hm hl hk a ε ha hε_lo hε_hi f hf0 hf1)).1
  exact digit_of_evenClosed_coeff g (by omega) t ht0 m _ hclosed n hn

end Erdos482.General
