import Erdos482.General.St06Thm33

/-!
# Stoll [St06] Theorem 3.4 — the second binary (`g = 2`) family, at `ε = ½`

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125**
(2006), 89–100, Theorem 3.4.  Same recurrence shape as Theorem 3.3 (`St06Thm33.lean`) but with
`a = 2k+1 + 2l/(t+2m)` (the numerator is `2l`, not `t+2l`) and `1 ≤ l ≤ m`.

> `u₁ = m`, `u_{n+1} = ⌊a·(uₙ + ε)⌋` (`n` odd), `u_{n+1} = ⌊b·(uₙ + ½)⌋` (`n` even), `b = 2/a`.

i.e. **`ε` sits on the `a`-step** (the odd→even paper step that Stoll varies) and `½` on the `b`-step.
In our 0-indexed `St06Example.su a b ε s m` this is `su a b ε (1/2) m` (`ε` enters at `Even n`).

**Closed forms** (`su a b ε (1/2) m`, verified `0/4000` random `(m,l,k,t)`):
* odd   `su(2j)   = m·2ʲ + ⌊t·2ʲ/2⌋`                         (the universal odd form),
* even  `su(2j+1) = (2k+1)·(m·2ʲ+⌊t·2ʲ/2⌋) + k + l·2ʲ`.

Conclusion (1) — `su(2n) − 2·su(2n−2) = nth binary digit of w` — is then `digit_of_evenClosed_coeff`
at `g=2, c=m`, identical to Theorem 3.3.

**ε-interval — the GENUINE, full, `t`-universal interval** (`st06_thm34_astep_eps`,
`st06_thm34_closed_eps`, `st06_thm34_digits_eps`, `st06_thm34_isBit_eps`).  Conclusion (1) holds for
**every** `ε` in Stoll's printed symmetric interval

> `½ − (m−l+½)/D₁  ≤  ε  <  ½ + (m−l+½)/D₁`,   `D₁ = (2m+1)(2k+1)+2l`,

uniformly over all real `w > 0` (`t ∈ [1,2)`).  No Diophantine / equidistribution input: the `a`-step
floor bracket `0 ≤ Dε − (t+2m)k + l(2B − t·s) < t+2m` is bounded by the **independent** worst cases of
`t ∈ [1,2)` and `2B − t·s ∈ (−2,0]`, both binding at `t=1` (hence the `D₁` denominator).

**⚠️ Historical note — the `ε`-on-`b`-step "obstruction" theorems below**
(`st06_thm34_bstep_value/band`, `st06_thm34_band_fails_below/above_half`) study a **different**
recurrence: `ε` on the `b`-step, `½` on the `a`-step — that is Theorem **3.3**'s placement, with `ε ↔ ½`
**swapped** from Theorem 3.4.  They are sound Lean (axiom-clean) but say **nothing** about Theorem 3.4;
their "only `ε = ½` works" conclusion is an artifact of putting `ε` on the genuinely non-uniform step.
The ON-LINE findings (2026-06-13, `archive/findings/`) caught this.  The honest Theorem 3.4 result is
the full interval above — kept the swapped theorems as a documented contrast (a faithful proof of an
*unfaithful* statement; `#print axioms` clean says nothing about statement-faithfulness).  Axiom-clean.
-/

namespace Erdos482.General

open Real

/-- **Thm 3.4 `a`-step floor crux** (unconditional).  `⌊a(A+½)⌋ = (2k+1)A + k + l·s`, reducing to
`0 ≤ ½ + l(1 − t·s + 2B)/(t+2m) < 1`, bounded by `1 ≤ l ≤ m` and the floor bounds `2B ≤ t·s < 2B+2`. -/
theorem st06_thm34_acrux
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (s : ℤ) (hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (a : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) :
    ⌊a * (((m * s + B : ℤ) : ℝ) + 1 / 2)⌋ = (2 * k + 1) * (m * s + B) + k + l * s := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hlmR : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hdenne : t + 2 * m ≠ 0 := ne_of_gt hden
  have h2B_le : (2 * B : ℝ) ≤ t * s := by linarith
  have hts_lt : t * s < 2 * B + 2 := by linarith
  rw [Int.floor_eq_iff]
  set E : ℤ := (2 * k + 1) * (m * s + B) + k + l * s with hE
  have hN : (t + 2 * m) * (a * (((m * s + B : ℤ) : ℝ) + 1 / 2) - (E : ℝ))
      = (t + 2 * m) / 2 + l * (1 - t * s + 2 * B) := by
    rw [ha, hE]; push_cast; field_simp; ring
  have harg : a * (((m * s + B : ℤ) : ℝ) + 1 / 2) - (E : ℝ)
      = ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) / (t + 2 * m) := by
    rw [eq_div_iff hdenne, mul_comm]; exact hN
  set q : ℝ := ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) / (t + 2 * m) with hq
  have hq0 : 0 ≤ q := by
    rw [hq]; apply div_nonneg _ (le_of_lt hden); nlinarith [h2B_le, hts_lt, hl1R, hlmR, hmR, ht1]
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hden]; nlinarith [h2B_le, hts_lt, hl1R, hlmR, hmR, ht1]
  exact ⟨by linarith [harg], by linarith [harg]⟩

set_option maxHeartbeats 1000000 in
/-- **Thm 3.4 GENUINE `a`-step floor crux at general `ε`** (Stoll's actual Theorem 3.4 — `ε` sits on
the `a`-step, the odd→even paper step, with `½` on the `b`-step; see `St06Example.su`).  For every
`ε` in Stoll's printed **symmetric** interval

  `½ − (m−l+½)/D₁  ≤  ε  <  ½ + (m−l+½)/D₁`,   `D₁ = (2m+1)(2k+1)+2l`,

the `a`-step lands on the digit value `(2k+1)A + k + l·s` for **every** `t ∈ [1,2)` (uniform / `t`-
universal — no Diophantine input).  The two endpoints are the independent worst cases of the floor
bracket `0 ≤ Dε − (t+2m)k + l(2B − t·s) < t+2m` (`D = (t+2m)(2k+1)+2l`, `2B − t·s ∈ (−2,0]`): the
lower over `t→1, 2B−t·s→−2`, the upper over `t→1, 2B−t·s→0` — both binding at `t=1`, giving the
`D₁`-denominator interval.  This is the result the ON-LINE findings (2026-06-13) flagged as the honest
Theorem 3.4 — genuinely formalizable (unlike the pair-5 `ε`-on-`b`-step obstruction below). -/
theorem st06_thm34_astep_eps
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (s : ℤ) (hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (a : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l)) :
    ⌊a * (((m * s + B : ℤ) : ℝ) + ε)⌋ = (2 * k + 1) * (m * s + B) + k + l * s := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hlmR : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hdenne : t + 2 * m ≠ 0 := ne_of_gt hden
  have h2B_le : (2 * B : ℝ) ≤ t * s := by linarith
  have hts_lt : t * s < 2 * B + 2 := by linarith
  -- clean `ε`-bounds: clear the `D₁` denominator (worst-case denominator at `t=1`)
  have hD1pos : (0 : ℝ) < (2 * (m : ℝ) + 1) * (2 * k + 1) + 2 * l := by nlinarith [hmR, hkR, hl1R]
  have heq_lo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l)
      = ((2 * (m : ℝ) + 1) * k + 2 * l) / ((2 * m + 1) * (2 * k + 1) + 2 * l) := by
    rw [eq_div_iff (ne_of_gt hD1pos), sub_mul, div_mul_cancel₀ _ (ne_of_gt hD1pos)]; ring
  have heq_hi : (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l)
      = ((2 * (m : ℝ) + 1) * (k + 1)) / ((2 * m + 1) * (2 * k + 1) + 2 * l) := by
    rw [eq_div_iff (ne_of_gt hD1pos), add_mul, div_mul_cancel₀ _ (ne_of_gt hD1pos)]; ring
  rw [heq_lo] at hεlo
  rw [heq_hi] at hεhi
  have hlo' : (2 * (m : ℝ) + 1) * k + 2 * l ≤ ε * ((2 * m + 1) * (2 * k + 1) + 2 * l) :=
    (div_le_iff₀ hD1pos).mp hεlo
  have hhi' : ε * ((2 * m + 1) * (2 * k + 1) + 2 * l) < (2 * (m : ℝ) + 1) * (k + 1) :=
    (lt_div_iff₀ hD1pos).mp hεhi
  -- key consequence: `(2k+1)ε − k ≥ 0` (ε is above `k/(2k+1)`)
  have hek : (0 : ℝ) ≤ (2 * k + 1) * ε - k := by
    have hmul : (0 : ℝ) ≤ ((2 * m + 1) * (2 * k + 1) + 2 * l) * ((2 * k + 1) * ε - k) := by
      nlinarith [mul_le_mul_of_nonneg_left hlo' (show (0 : ℝ) ≤ 2 * (k : ℝ) + 1 by linarith),
        hl1R, hkR]
    exact (mul_nonneg_iff_of_pos_left hD1pos).mp hmul
  -- and the mirror: `(k+1) − (2k+1)ε ≥ 0` (ε is below `(k+1)/(2k+1)`)
  have hek2 : (0 : ℝ) ≤ (k + 1) - (2 * k + 1) * ε := by
    have hmul : (0 : ℝ) ≤ ((2 * m + 1) * (2 * k + 1) + 2 * l) * ((k + 1) - (2 * k + 1) * ε) := by
      nlinarith [mul_lt_mul_of_pos_left hhi' (show (0 : ℝ) < 2 * (k : ℝ) + 1 by linarith),
        hl1R, hkR]
    exact (mul_nonneg_iff_of_pos_left hD1pos).mp hmul
  rw [Int.floor_eq_iff]
  set E : ℤ := (2 * k + 1) * (m * s + B) + k + l * s with hE
  have hN : (t + 2 * m) * (a * (((m * s + B : ℤ) : ℝ) + ε) - (E : ℝ))
      = ((t + 2 * m) * (2 * k + 1) + 2 * l) * ε - (t + 2 * m) * k + l * (2 * B - t * s) := by
    rw [ha, hE]; push_cast; field_simp; ring
  have harg : a * (((m * s + B : ℤ) : ℝ) + ε) - (E : ℝ)
      = (((t + 2 * m) * (2 * k + 1) + 2 * l) * ε - (t + 2 * m) * k + l * (2 * B - t * s))
          / (t + 2 * m) := by
    rw [eq_div_iff hdenne, mul_comm]; exact hN
  set q : ℝ := (((t + 2 * m) * (2 * k + 1) + 2 * l) * ε - (t + 2 * m) * k + l * (2 * B - t * s))
      / (t + 2 * m) with hq
  have hq0 : 0 ≤ q := by
    rw [hq]; apply div_nonneg _ (le_of_lt hden)
    nlinarith [hlo', mul_nonneg (show (0 : ℝ) ≤ t - 1 by linarith) hek,
      mul_nonneg (show (0 : ℝ) ≤ (l : ℝ) by linarith) (show (0 : ℝ) ≤ 2 * B + 2 - t * s by linarith)]
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hden]
    nlinarith [hhi', mul_nonneg (show (0 : ℝ) ≤ t - 1 by linarith) hek2,
      mul_nonneg (show (0 : ℝ) ≤ (l : ℝ) by linarith) (show (0 : ℝ) ≤ t * s - 2 * B by linarith)]
  exact ⟨by linarith [harg], by linarith [harg]⟩

set_option maxHeartbeats 800000 in
/-- **Thm 3.4 `b`-step floor crux** at `ε = ½`.  From the even form `E' = (2k+1)A + k + l·s`, the
`(b, ½)` floor lands on the next odd value `2ms + C`.  Same engine as `st06_thm33_bcrux`, with
`Da = (2k+1)(t+2m)+2l` and `Nq = (t+2m)/2 + l(1 − t·s + 2B)`; both digit-branches close with room. -/
theorem st06_thm34_bcrux
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (s : ℤ) (hs : 1 ≤ s)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B C : ℤ) (hB : (B : ℝ) ≤ t * s / 2) (hB' : t * s / 2 < B + 1)
    (hC : (C : ℝ) ≤ t * s) (hC' : t * s < C + 1)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) :
    ⌊b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * (1 / 2)⌋ = 2 * m * s + C := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hlmR : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hdenne : t + 2 * m ≠ 0 := ne_of_gt hden
  have hfrac_pos : (0 : ℝ) < 2 * l / (t + 2 * m) := div_pos (by linarith) hden
  have ha_pos : (0 : ℝ) < a := by rw [ha]; linarith
  have hane : a ≠ 0 := ne_of_gt ha_pos
  have h2B_le : (2 * B : ℝ) ≤ t * s := by linarith
  have h2BC : 2 * B ≤ C := by
    have hle : (2 * B : ℤ) ≤ ⌊t * s⌋ := Int.le_floor.mpr (by push_cast; linarith)
    have hCeq : ⌊t * s⌋ = C := by rw [Int.floor_eq_iff]; exact ⟨hC, by linarith⟩
    omega
  have hCle : C ≤ 2 * B + 1 := by
    have : (C : ℤ) < 2 * B + 2 := by
      have : (C : ℝ) < 2 * B + 2 := by linarith
      exact_mod_cast this
    omega
  set Da : ℝ := (2 * k + 1) * (t + 2 * m) + 2 * l with hDa
  have hDa_pos : (0 : ℝ) < Da := by rw [hDa]; nlinarith [hkR, hden, ht1, hl1R]
  have hDane : Da ≠ 0 := ne_of_gt hDa_pos
  have ha_eq : a = Da / (t + 2 * m) := by rw [ha, hDa]; field_simp
  have hb_eq : b = 2 * (t + 2 * m) / Da := by rw [hb, ha_eq, div_div_eq_mul_div]
  set y : ℝ := t * s - C with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hy1 : y < 1 := by rw [hy]; linarith
  have hcase : (C : ℝ) - 2 * B = 0 ∨ (C : ℝ) - 2 * B = 1 := by
    rcases (show C - 2 * B = 0 ∨ C - 2 * B = 1 from by omega) with hd | hd
    · left; have : ((C - 2 * B : ℤ) : ℝ) = 0 := by rw [hd]; norm_num
      push_cast at this; linarith
    · right; have : ((C - 2 * B : ℤ) : ℝ) = 1 := by rw [hd]; norm_num
      push_cast at this; linarith
  set Nq : ℝ := (t + 2 * m) / 2 + l * (1 - t * s + 2 * B) with hNq
  have hclear : (t + 2 * m) * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ)
      = Da * (((m * s + B : ℤ) : ℝ) + 1 / 2) - Nq := by
    rw [hDa, hNq]; push_cast; ring
  have hval : b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * (1 / 2)
      = 2 * (((m * s + B : ℤ) : ℝ)) + 1 - (2 * Nq - 2 * (t + 2 * m) * (1 / 2)) / Da := by
    rw [hb_eq]
    rw [show 2 * (t + 2 * m) / Da * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ)
          + 2 * (t + 2 * m) / Da * (1 / 2)
        = (2 * (t + 2 * m) * ((((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + 1 / 2)) / Da from by
      ring]
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hDane]
    linear_combination (2 : ℝ) * hclear
  -- the two key bounds (with `s` cancelled — only `y ∈ [0,1)` remains)
  have hts_lt2 : t * s < 2 * B + 2 := by linarith [hB']
  have hpkD : (0 : ℝ) ≤ (k : ℝ) * (t + 2 * m) := mul_nonneg hkR (le_of_lt hden)
  have hpL : (0 : ℝ) ≤ (l : ℝ) * (t * s - 2 * B) := mul_nonneg (by linarith) (by linarith [h2B_le])
  have hpU : (0 : ℝ) ≤ (l : ℝ) * (2 * B + 2 - t * s) := mul_nonneg (by linarith) (by linarith [hts_lt2])
  have hL : 2 * Nq - 2 * (t + 2 * m) * (1 / 2) ≤ (1 - ((C : ℝ) - 2 * B)) * Da := by
    rw [hNq, hDa]
    rcases hcase with hd | hd <;> nlinarith [hd, hC, hC', hl1R, hlmR, hmR, ht1, hkR, hpkD, hpL, hpU]
  have hU : -(((C : ℝ) - 2 * B)) * Da < 2 * Nq - 2 * (t + 2 * m) * (1 / 2) := by
    rw [hNq, hDa]
    rcases hcase with hd | hd <;> nlinarith [hd, hC, hC', hl1R, hlmR, hmR, ht1, hkR, hpkD, hpL, hpU]
  rw [Int.floor_eq_iff, hval]
  have hfrac_lo : (2 * Nq - 2 * (t + 2 * m) * (1 / 2)) / Da ≤ 1 - ((C : ℝ) - 2 * B) :=
    (div_le_iff₀ hDa_pos).mpr (by linarith [hL])
  have hfrac_hi : -(((C : ℝ) - 2 * B)) < (2 * Nq - 2 * (t + 2 * m) * (1 / 2)) / Da :=
    (lt_div_iff₀ hDa_pos).mpr (by linarith [hU])
  constructor
  · push_cast; linarith [hfrac_lo]
  · push_cast; linarith [hfrac_hi]

/-- **[SWAPPED-VARIANT, NOT Stoll's Theorem 3.4 — see module header.]** general-`ε` b-step value.
This studies `ε` on the **b-step** (`½` on the a-step), which is Theorem **3.3**'s placement; Stoll's
3.4 puts `ε` on the a-step (`st06_thm34_astep_eps`).  For *any* `ε`, the even→odd b-step value has the
closed form `2(ms+B) + 1 − frac`, with `frac = (2·Nq − 2(t+2m)ε)/Da`, `Nq = (t+2m)/2 + l(1 − t·s + 2B)`,
`Da = (2k+1)(t+2m) + 2l`.  Isolates the exact dependence on `ε` (the `ε = ½` crux is the case where
`frac` lands in the admissible band for *every* fractional part). -/
theorem st06_thm34_bstep_value
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (s : ℤ)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B : ℤ) (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ) :
    b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * ε
      = 2 * ((m * s + B : ℤ) : ℝ) + 1
        - (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
            / ((2 * k + 1) * (t + 2 * m) + 2 * l) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have ha_pos : (0 : ℝ) < a := by rw [ha]; have := div_pos (by linarith : (0:ℝ) < 2 * l) hden; linarith
  have hane : a ≠ 0 := ne_of_gt ha_pos
  set Da : ℝ := (2 * k + 1) * (t + 2 * m) + 2 * l with hDa
  have hDa_pos : (0 : ℝ) < Da := by rw [hDa]; nlinarith [hkR, hden, ht1, hl1R]
  have hDane : Da ≠ 0 := ne_of_gt hDa_pos
  have ha_eq : a = Da / (t + 2 * m) := by rw [ha, hDa]; field_simp
  have hb_eq : b = 2 * (t + 2 * m) / Da := by rw [hb, ha_eq, div_div_eq_mul_div]
  set Nq : ℝ := (t + 2 * m) / 2 + l * (1 - t * s + 2 * B) with hNq
  have hclear : (t + 2 * m) * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ)
      = Da * (((m * s + B : ℤ) : ℝ) + 1 / 2) - Nq := by
    rw [hDa, hNq]; push_cast; ring
  rw [hb_eq]
  rw [show 2 * (t + 2 * m) / Da * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ)
        + 2 * (t + 2 * m) / Da * ε
      = (2 * (t + 2 * m) * ((((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + ε)) / Da from by ring]
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hDane]
  linear_combination (2 : ℝ) * hclear

/-- **[SWAPPED-VARIANT, NOT Stoll's Theorem 3.4 — see module header.]** general-`ε` b-step band (the
precise ε-condition; the analogue of `pair5_estep_band`).  `ε` is on the **b-step** here (Thm 3.3's
placement), so the "obstruction" below is real for *this* recurrence but irrelevant to Theorem 3.4.
With `d = C − 2B ∈ {0,1}` the b-step lands on the digit value `2ms + C` **iff** `frac ∈ (−d, 1−d]`,
where `frac = (2·Nq − 2(t+2m)ε)/Da`.  At `ε = ½` this band is satisfied for every fractional part
(`st06_thm34_bcrux`); for `ε ≠ ½` the `d = 0` (large `t·s − 2B`) and `d = 1` (small `t·s − 2B`)
branches pull in opposite directions, so no single `ε ≠ ½` works for all `w` for this b-step variant. -/
theorem st06_thm34_bstep_band
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (s : ℤ)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B C : ℤ) (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ) :
    ⌊b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * ε⌋ = 2 * m * s + C
      ↔ -((C : ℝ) - 2 * B)
            < (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
                / ((2 * k + 1) * (t + 2 * m) + 2 * l)
          ∧ (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
                / ((2 * k + 1) * (t + 2 * m) + 2 * l) ≤ 1 - ((C : ℝ) - 2 * B) := by
  rw [st06_thm34_bstep_value t ht1 ht2 s m l k hm hl1 hlm hk B a b ha hb ε, Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩; push_cast at h1 h2; constructor <;> linarith
  · rintro ⟨h1, h2⟩; push_cast; constructor <;> linarith

/-- **[SWAPPED-VARIANT, NOT Stoll's Theorem 3.4 — see module header.]** b-step obstruction, ε < ½.
On a `d = 1` digit step (`C = 2B+1`) with `t·s` close to the boundary (`2l(t·s − C) < (t+2m)(1−2ε)`),
this *b-step* variant does **not** land on `2ms + C`: `frac > 0 = 1−d` breaks the band's upper bound.
So no `ε < ½` works for the b-step variant (cf. `pair5_band_fails_below_half`).  Genuine Theorem 3.4
(ε on the a-step) has no such obstruction — its full interval is `st06_thm34_digits_eps`. -/
theorem st06_thm34_band_fails_below_half
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (s : ℤ)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B C : ℤ) (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ)
    (hd : (C : ℝ) = 2 * B + 1) (hy0 : (C : ℝ) ≤ t * s)
    (hsmall : 2 * l * (t * s - C) < (t + 2 * m) * (1 - 2 * ε)) :
    ⌊b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * ε⌋ ≠ 2 * m * s + C := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hDa_pos : (0 : ℝ) < (2 * k + 1) * (t + 2 * m) + 2 * l := by nlinarith [hkR, hden, ht1, hl1R]
  rw [Ne, st06_thm34_bstep_band t ht1 ht2 s m l k hm hl1 hlm hk B C a b ha hb ε]
  rintro ⟨-, hhi⟩
  have hnum : 0 < 2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε := by
    nlinarith [hsmall, hd]
  have hfrac : 0 < (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
      / ((2 * k + 1) * (t + 2 * m) + 2 * l) := div_pos hnum hDa_pos
  -- but the band's upper bound forces frac ≤ 1 − (C − 2B) = 0
  have : (1 : ℝ) - ((C : ℝ) - 2 * B) = 0 := by rw [hd]; ring
  linarith [hhi, hfrac, this]

/-- **[SWAPPED-VARIANT, NOT Stoll's Theorem 3.4 — see module header.]** b-step obstruction, ε > ½.
On a `d = 0` digit step (`C = 2B`) with `t·s` close to the upper boundary
(`(t+2m)(2ε−1) > 2l(2B+1 − t·s)`), this *b-step* variant does **not** land on `2ms + C`: `frac < 0 = −d`
breaks the band's lower bound.  So no `ε > ½` works for the b-step variant either (cf.
`pair5_band_fails_above_half`).  Genuine Theorem 3.4 (ε on the a-step) has no such obstruction. -/
theorem st06_thm34_band_fails_above_half
    (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) (s : ℤ)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (B C : ℤ) (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ)
    (hd : (C : ℝ) = 2 * B) (hy1 : t * s < C + 1)
    (hbig : (t + 2 * m) * (2 * ε - 1) > 2 * l * (2 * B + 1 - t * s)) :
    ⌊b * (((2 * k + 1) * (m * s + B) + k + l * s : ℤ) : ℝ) + b * ε⌋ ≠ 2 * m * s + C := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < t + 2 * m := by linarith
  have hDa_pos : (0 : ℝ) < (2 * k + 1) * (t + 2 * m) + 2 * l := by nlinarith [hkR, hden, ht1, hl1R]
  rw [Ne, st06_thm34_bstep_band t ht1 ht2 s m l k hm hl1 hlm hk B C a b ha hb ε]
  rintro ⟨hlo, -⟩
  have hnum : 2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε < 0 := by
    nlinarith [hbig, hd]
  have hfrac : (2 * ((t + 2 * m) / 2 + l * (1 - t * s + 2 * B)) - 2 * (t + 2 * m) * ε)
      / ((2 * k + 1) * (t + 2 * m) + 2 * l) < 0 := div_neg_of_neg_of_pos hnum hDa_pos
  have : -((C : ℝ) - 2 * B) = 0 := by rw [hd]; ring
  linarith [hlo, hfrac, this]

/-- **St06 Theorem 3.4 — joint closed forms** at `ε = ½` (binary, second family). -/
theorem st06_thm34_closed (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) :
    (∀ j, su a b (1 / 2) (1 / 2) m (2 * j) = m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) ∧
      (∀ j, su a b (1 / 2) (1 / 2) m (2 * j + 1)
        = (2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j) := by
  have hone : ∀ j : ℕ, (1 : ℤ) ≤ 2 ^ j := fun j => one_le_pow₀ (by norm_num)
  have hsR : ∀ j : ℕ, ((2 ^ j : ℤ) : ℝ) = (2 : ℝ) ^ j := fun j => by push_cast; ring
  have hA : ∀ j, su a b (1 / 2) (1 / 2) m (2 * j) = m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋ := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.mul_zero, su_zero, pow_zero, mul_one]
      have hfl : ⌊t / (2 : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
      rw [hfl]; ring
    | succ j ih =>
      have hB : ((⌊t * (2 : ℝ) ^ j / 2⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) / 2 := by
        rw [hsR]; exact Int.floor_le _
      have hB' : t * ((2 ^ j : ℤ) : ℝ) / 2 < ⌊t * (2 : ℝ) ^ j / 2⌋ + 1 := by
        rw [hsR]; exact Int.lt_floor_add_one _
      have hC : ((⌊t * (2 : ℝ) ^ j⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) := by
        rw [hsR]; exact Int.floor_le _
      have hC' : t * ((2 ^ j : ℤ) : ℝ) < ⌊t * (2 : ℝ) ^ j⌋ + 1 := by
        rw [hsR]; exact Int.lt_floor_add_one _
      have hsu1 : su a b (1 / 2) (1 / 2) m (2 * j + 1)
          = (2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j := by
        rw [su_succ, if_pos ⟨j, two_mul j⟩, ih]
        exact st06_thm34_acrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl1 hlm hk
          ⌊t * (2 : ℝ) ^ j / 2⌋ hB hB' a ha
      have hsu2 : su a b (1 / 2) (1 / 2) m (2 * (j + 1)) = 2 * m * 2 ^ j + ⌊t * (2 : ℝ) ^ j⌋ := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring, su_succ,
          if_neg (by simp [parity_simps]), hsu1]
        have := st06_thm34_bcrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl1 hlm hk
          ⌊t * (2 : ℝ) ^ j / 2⌋ ⌊t * (2 : ℝ) ^ j⌋ hB hB' hC hC' a b ha hb
        rw [show b * ((((2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j : ℤ) : ℝ) + 1 / 2)
            = b * (((2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j : ℤ) : ℝ)
              + b * (1 / 2) from by ring]
        exact this
      have hfl2 : ⌊t * (2 : ℝ) ^ (j + 1) / 2⌋ = ⌊t * (2 : ℝ) ^ j⌋ := by
        congr 1; rw [pow_succ]; ring
      rw [hsu2, hfl2, pow_succ]; ring
  refine ⟨hA, fun j => ?_⟩
  have hB : ((⌊t * (2 : ℝ) ^ j / 2⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) / 2 := by
    rw [hsR]; exact Int.floor_le _
  have hB' : t * ((2 ^ j : ℤ) : ℝ) / 2 < ⌊t * (2 : ℝ) ^ j / 2⌋ + 1 := by
    rw [hsR]; exact Int.lt_floor_add_one _
  rw [su_succ, if_pos ⟨j, two_mul j⟩, hA j]
  exact st06_thm34_acrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl1 hlm hk
    ⌊t * (2 : ℝ) ^ j / 2⌋ hB hB' a ha

/-- **St06 Theorem 3.4, conclusion (1)** at `ε = ½` — the odd-index Graham–Pollak difference reads
off `w`'s `n`-th binary digit, for every real `w > 0` (here `t = w/2^M ∈ [1,2)`). -/
theorem st06_thm34_digits (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) (1 / 2) m (2 * n) - 2 * su a b (1 / 2) (1 / 2) m (2 * n - 2)
      = ((Real.digits (t * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hclosed := (st06_thm34_closed t ht1 ht2 m l k hm hl1 hlm hk a b ha hb).1
  have := digit_of_evenClosed_coeff 2 (le_refl 2) t ht0 m _ hclosed n hn
  simpa using this

/-- **St06 Theorem 3.4 — the Graham–Pollak difference is a genuine bit** (`0` or `1`), at `ε = ½`. -/
theorem st06_thm34_isBit (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) (1 / 2) m (2 * n) - 2 * su a b (1 / 2) (1 / 2) m (2 * n - 2) = 0 ∨
      su a b (1 / 2) (1 / 2) m (2 * n) - 2 * su a b (1 / 2) (1 / 2) m (2 * n - 2) = 1 := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  rw [st06_thm34_digits t ht0 ht1 ht2 m l k hm hl1 hlm hk a b ha hb n hn,
    realDigits_eq_digitStep 2 (t * (2 : ℝ) ^ (n - 1) / 2) (by positivity) 0]
  simp only [pow_zero, mul_one]
  obtain ⟨h0, h2⟩ := digitStep_mem 2 (by norm_num) (t * (2 : ℝ) ^ (n - 1) / 2)
  omega

/-- **St06 Theorem 3.4, conclusion (2)** at `ε = ½` — the even-index Graham–Pollak difference:
`su(2n+1) − 2·su(2n−1) = (2k+1)·dₙ − k`, where `dₙ = ⌊t·2^{n−1}⌋ − 2⌊t·2^{n−1}/2⌋` is the `n`-th
binary digit.  (Pure algebra from the even closed form; the `l·2ʲ` term telescopes away.) -/
theorem st06_thm34_even_digits (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a)
    (n : ℕ) (hn : 1 ≤ n) :
    su a b (1 / 2) (1 / 2) m (2 * n + 1) - 2 * su a b (1 / 2) (1 / 2) m (2 * n - 1)
      = (2 * k + 1) * (⌊t * (2 : ℝ) ^ (n - 1)⌋ - 2 * ⌊t * (2 : ℝ) ^ (n - 1) / 2⌋) - k := by
  have hE := (st06_thm34_closed t ht1 ht2 m l k hm hl1 hlm hk a b ha hb).2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hfl : ⌊t * (2 : ℝ) ^ (n' + 1) / 2⌋ = ⌊t * (2 : ℝ) ^ n'⌋ := by congr 1; rw [pow_succ]; ring
  rw [hE (n' + 1), show 2 * (n' + 1) - 1 = 2 * n' + 1 from by omega, hE n',
    show n' + 1 - 1 = n' from by omega, hfl, pow_succ]
  ring

/-! ## The GENUINE full-interval Theorem 3.4 (every `ε` in Stoll's printed symmetric interval)

The theorems below are Stoll's actual Theorem 3.4: the recurrence is `su a b ε (1/2) m` — `ε` on the
`a`-step (the offset Stoll varies), `½` on the `b`-step — and the conclusion holds for **every** `ε`
in the printed symmetric interval, uniformly over `w` (i.e. `t ∈ [1,2)`).  This is the genuine
content the ON-LINE findings (2026-06-13) identified: the `ε`-on-`b`-step obstruction theorems above
(`st06_thm34_band_fails_*`) are about a *different* recurrence (`3.3`-placement, `ε ↔ ½` swapped) and
say nothing about Theorem 3.4.  Here the interval is a real theorem, not a single point. -/

/-- **St06 Theorem 3.4 — joint closed forms, full interval.**  For every `ε` in Stoll's symmetric
interval `½ ± (m−l+½)/((2m+1)(2k+1)+2l)`, the recurrence `su a b ε (1/2) m` (ε on the a-step) has the
same closed forms as the `ε = ½` case — the a-step floor lands on `(2k+1)A+k+l·s` for every such ε. -/
theorem st06_thm34_closed_eps (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l)) :
    (∀ j, su a b ε (1 / 2) m (2 * j) = m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) ∧
      (∀ j, su a b ε (1 / 2) m (2 * j + 1)
        = (2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j) := by
  have hone : ∀ j : ℕ, (1 : ℤ) ≤ 2 ^ j := fun j => one_le_pow₀ (by norm_num)
  have hsR : ∀ j : ℕ, ((2 ^ j : ℤ) : ℝ) = (2 : ℝ) ^ j := fun j => by push_cast; ring
  have hA : ∀ j, su a b ε (1 / 2) m (2 * j) = m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋ := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.mul_zero, su_zero, pow_zero, mul_one]
      have hfl : ⌊t / (2 : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff, Set.mem_Ico]; constructor <;> linarith
      rw [hfl]; ring
    | succ j ih =>
      have hB : ((⌊t * (2 : ℝ) ^ j / 2⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) / 2 := by
        rw [hsR]; exact Int.floor_le _
      have hB' : t * ((2 ^ j : ℤ) : ℝ) / 2 < ⌊t * (2 : ℝ) ^ j / 2⌋ + 1 := by
        rw [hsR]; exact Int.lt_floor_add_one _
      have hC : ((⌊t * (2 : ℝ) ^ j⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) := by
        rw [hsR]; exact Int.floor_le _
      have hC' : t * ((2 ^ j : ℤ) : ℝ) < ⌊t * (2 : ℝ) ^ j⌋ + 1 := by
        rw [hsR]; exact Int.lt_floor_add_one _
      have hsu1 : su a b ε (1 / 2) m (2 * j + 1)
          = (2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j := by
        rw [su_succ, if_pos ⟨j, two_mul j⟩, ih]
        exact st06_thm34_astep_eps t ht1 ht2 (2 ^ j) (hone j) m l k hm hl1 hlm hk
          ⌊t * (2 : ℝ) ^ j / 2⌋ hB hB' a ha ε hεlo hεhi
      have hsu2 : su a b ε (1 / 2) m (2 * (j + 1)) = 2 * m * 2 ^ j + ⌊t * (2 : ℝ) ^ j⌋ := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring, su_succ,
          if_neg (by simp [parity_simps]), hsu1]
        have := st06_thm34_bcrux t ht1 ht2 (2 ^ j) (hone j) m l k hm hl1 hlm hk
          ⌊t * (2 : ℝ) ^ j / 2⌋ ⌊t * (2 : ℝ) ^ j⌋ hB hB' hC hC' a b ha hb
        rw [show b * ((((2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j : ℤ) : ℝ) + 1 / 2)
            = b * (((2 * k + 1) * (m * 2 ^ j + ⌊t * (2 : ℝ) ^ j / 2⌋) + k + l * 2 ^ j : ℤ) : ℝ)
              + b * (1 / 2) from by ring]
        exact this
      have hfl2 : ⌊t * (2 : ℝ) ^ (j + 1) / 2⌋ = ⌊t * (2 : ℝ) ^ j⌋ := by
        congr 1; rw [pow_succ]; ring
      rw [hsu2, hfl2, pow_succ]; ring
  refine ⟨hA, fun j => ?_⟩
  have hB : ((⌊t * (2 : ℝ) ^ j / 2⌋ : ℤ) : ℝ) ≤ t * ((2 ^ j : ℤ) : ℝ) / 2 := by
    rw [hsR]; exact Int.floor_le _
  have hB' : t * ((2 ^ j : ℤ) : ℝ) / 2 < ⌊t * (2 : ℝ) ^ j / 2⌋ + 1 := by
    rw [hsR]; exact Int.lt_floor_add_one _
  rw [su_succ, if_pos ⟨j, two_mul j⟩, hA j]
  exact st06_thm34_astep_eps t ht1 ht2 (2 ^ j) (hone j) m l k hm hl1 hlm hk
    ⌊t * (2 : ℝ) ^ j / 2⌋ hB hB' a ha ε hεlo hεhi

/-- **St06 Theorem 3.4, conclusion (1) — full interval.**  For **every** `ε` in Stoll's symmetric
interval, the odd-index Graham–Pollak difference of `su a b ε (1/2) m` reads off `w`'s `n`-th binary
digit, uniformly over all real `w > 0` (`t ∈ [1,2)`).  This is the genuine `t`-universal Theorem 3.4. -/
theorem st06_thm34_digits_eps (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε (1 / 2) m (2 * n) - 2 * su a b ε (1 / 2) m (2 * n - 2)
      = ((Real.digits (t * (2 : ℝ) ^ (n - 1) / 2) 2 0 : ℕ) : ℤ) := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hclosed := (st06_thm34_closed_eps t ht1 ht2 m l k hm hl1 hlm hk a b ha hb ε hεlo hεhi).1
  have := digit_of_evenClosed_coeff 2 (le_refl 2) t ht0 m _ hclosed n hn
  simpa using this

/-- **St06 Theorem 3.4 — the Graham–Pollak difference is a genuine bit** (`0` or `1`), for every `ε`
in Stoll's symmetric interval (full-interval version). -/
theorem st06_thm34_isBit_eps (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε (1 / 2) m (2 * n) - 2 * su a b ε (1 / 2) m (2 * n - 2) = 0 ∨
      su a b ε (1 / 2) m (2 * n) - 2 * su a b ε (1 / 2) m (2 * n - 2) = 1 := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  rw [st06_thm34_digits_eps t ht0 ht1 ht2 m l k hm hl1 hlm hk a b ha hb ε hεlo hεhi n hn,
    realDigits_eq_digitStep 2 (t * (2 : ℝ) ^ (n - 1) / 2) (by positivity) 0]
  simp only [pow_zero, mul_one]
  obtain ⟨h0, h2⟩ := digitStep_mem 2 (by norm_num) (t * (2 : ℝ) ^ (n - 1) / 2)
  omega

/-- **St06 Theorem 3.4, conclusion (2) — full interval.**  For every `ε` in Stoll's symmetric
interval, the even-index Graham–Pollak difference of `su a b ε (1/2) m` is `(2k+1)·dₙ − k` with
`dₙ = ⌊t·2^{n−1}⌋ − 2⌊t·2^{n−1}/2⌋` the `n`-th binary digit (same closed form as the `ε = ½` case,
since the a-step lands on the same integer for every admissible `ε`). -/
theorem st06_thm34_even_digits_eps (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (m l k : ℤ) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m) (hk : 0 ≤ k)
    (a b : ℝ) (ha : a = (2 * k + 1) + 2 * l / (t + 2 * m)) (hb : b = 2 / a) (ε : ℝ)
    (hεlo : (1 : ℝ) / 2 - ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l) ≤ ε)
    (hεhi : ε < (1 : ℝ) / 2 + ((m : ℝ) - l + 1 / 2) / ((2 * m + 1) * (2 * k + 1) + 2 * l))
    (n : ℕ) (hn : 1 ≤ n) :
    su a b ε (1 / 2) m (2 * n + 1) - 2 * su a b ε (1 / 2) m (2 * n - 1)
      = (2 * k + 1) * (⌊t * (2 : ℝ) ^ (n - 1)⌋ - 2 * ⌊t * (2 : ℝ) ^ (n - 1) / 2⌋) - k := by
  have hE := (st06_thm34_closed_eps t ht1 ht2 m l k hm hl1 hlm hk a b ha hb ε hεlo hεhi).2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hfl : ⌊t * (2 : ℝ) ^ (n' + 1) / 2⌋ = ⌊t * (2 : ℝ) ^ n'⌋ := by congr 1; rw [pow_succ]; ring
  rw [hE (n' + 1), show 2 * (n' + 1) - 1 = 2 * n' + 1 from by omega, hE n',
    show n' + 1 - 1 = n' from by omega, hfl, pow_succ]
  ring

end Erdos482.General
