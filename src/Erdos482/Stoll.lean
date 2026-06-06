import Erdos482.Basic
import Erdos482.Crux
import Erdos482.Induction

/-!
# Stoll's Theorem 3.2 — the parametrized Graham–Pollak recurrence

Stoll (*A fancy way to obtain the binary digits of 759250125√2*, arXiv:0902.4168) generalizes the
Graham–Pollak sequence by varying the additive offset on the *odd* steps.  For `ε ∈ ℝ` define
`v₁ = 1`, and for `n ≥ 1`,

* `v_{n+1} = ⌊√2 (vₙ + ε)⌋`  when `n` is **odd**,
* `v_{n+1} = ⌊√2 (vₙ + ½)⌋`  when `n` is **even**.

For `ε` in the appropriate interval the difference `v_{2k+1} − 2 v_{2k−1}` reads off the binary
digits of `α√2` (Theorem 3.2 / Corollary 3.3).

We index `vv ε n := v_{n+1}` (0-indexed), so `vv ε 0 = v₁ = 1` and the step `vv ε (n+1)` from
`vv ε n` uses `ε` exactly when `n` is **even** (Stoll-index `n+1` odd).

**The clean invariant** (rederived & numerically verified — strictly simpler than the paper's
`(α,β,l,γ,t)` table form): writing `k = l + 2 + m`,

* `vv ε (2k−1) = ⌊α√2·2^m⌋   + α·2^(m+1)`     (Stoll eq (5))
* `vv ε (2k)   = ⌊α√2·2^(m+1)⌋ + α·2^(m+1)`   (Stoll eq (6))

The induction needs **only** `α : ℤ`, the `ε`-interval `[1−√2/2, √2/2)`, and a per-pair base case;
the `β, γ` and the relation `α+β = 2^(l+1)` from the paper are *not* needed for the digit-extraction
core (they only relabel `α√2`'s digits as the digits of `t = (α√2−β)/2^l`).  The `½`-step reduces to
`crux` (eq (7)); the `ε`-step reduces to `eq8_general` (eq (8)).
-/

namespace Erdos482
open Real

/-- Stoll's parametrized sequence, 0-indexed (`vv ε n = v_{n+1}`).  The step uses `ε` when `n` is
even, `½` when `n` is odd. -/
noncomputable def vv (ε : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => ⌊Real.sqrt 2 * ((vv ε n : ℝ) + (if Even n then ε else 1 / 2))⌋₊

/-- Recurrence over ℤ at an **even** index `n` (the `ε`-step). -/
private lemma vv_step_even (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (hn : Even n) :
    (vv ε (n + 1) : ℤ) = ⌊Real.sqrt 2 * ((vv ε n : ℝ) + ε)⌋ := by
  have h : vv ε (n + 1) = ⌊Real.sqrt 2 * ((vv ε n : ℝ) + ε)⌋₊ := by
    show ⌊Real.sqrt 2 * ((vv ε n : ℝ) + (if Even n then ε else 1 / 2))⌋₊ = _
    rw [if_pos hn]
  rw [h, Int.natCast_floor_eq_floor
    (mul_nonneg (Real.sqrt_nonneg 2) (add_nonneg (Nat.cast_nonneg _) hε))]

/-- Recurrence over ℤ at an **odd** index `n` (the `½`-step). -/
private lemma vv_step_odd (ε : ℝ) (n : ℕ) (hn : ¬ Even n) :
    (vv ε (n + 1) : ℤ) = ⌊Real.sqrt 2 * ((vv ε n : ℝ) + 1 / 2)⌋ := by
  have h : vv ε (n + 1) = ⌊Real.sqrt 2 * ((vv ε n : ℝ) + 1 / 2)⌋₊ := by
    show ⌊Real.sqrt 2 * ((vv ε n : ℝ) + (if Even n then ε else 1 / 2))⌋₊ = _
    rw [if_neg hn]
  rw [h, Int.natCast_floor_eq_floor
    (mul_nonneg (Real.sqrt_nonneg 2) (by positivity))]

/-- The `½`-step floor identity (generalizes `floorB`; reduces to `crux` at `α√2·2^(p+1)`):
from `⌊α√2·2^p⌋ + α·2^(p+1)` adding `½` gives `⌊α√2·2^(p+1)⌋ + α·2^(p+1)`. -/
private lemma stollB (a : ℤ) (p : ℕ) :
    ⌊Real.sqrt 2 * (((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ p⌋ + a * 2 ^ (p + 1) : ℤ) : ℝ) + 1 / 2)⌋
      = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (p + 1)⌋ + a * 2 ^ (p + 1) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨cl, cu⟩ := crux ((a : ℝ) * Real.sqrt 2 * 2 ^ (p + 1))
  have hhalf : (a : ℝ) * Real.sqrt 2 * 2 ^ (p + 1) / 2 = (a : ℝ) * Real.sqrt 2 * 2 ^ p := by ring
  rw [hhalf] at cl cu
  have key : Real.sqrt 2 * (((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ p⌋ + a * 2 ^ (p + 1) : ℤ) : ℝ) + 1 / 2)
      = ((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (p + 1)⌋ + a * 2 ^ (p + 1) : ℤ) : ℝ)
        + (Int.fract ((a : ℝ) * Real.sqrt 2 * 2 ^ (p + 1))
            - Real.sqrt 2 * Int.fract ((a : ℝ) * Real.sqrt 2 * 2 ^ p) + Real.sqrt 2 / 2) := by
    rw [← Int.self_sub_floor ((a : ℝ) * Real.sqrt 2 * 2 ^ (p + 1)),
      ← Int.self_sub_floor ((a : ℝ) * Real.sqrt 2 * 2 ^ p)]
    push_cast
    linear_combination (a : ℝ) * 2 ^ p * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨cl, cu⟩, add_zero]

/-- The `ε`-step floor identity (generalizes `floorA`; reduces to `eq8_general` at `α√2·2^q`):
from `⌊α√2·2^q⌋ + α·2^q` adding `ε` gives `⌊α√2·2^q⌋ + α·2^(q+1)`. -/
private lemma stollA (a : ℤ) (q : ℕ) {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε)
    (hε1 : ε < Real.sqrt 2 / 2) :
    ⌊Real.sqrt 2 * (((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ q⌋ + a * 2 ^ q : ℤ) : ℝ) + ε)⌋
      = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ q⌋ + a * 2 ^ (q + 1) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨el, eu⟩ := eq8_general hε0 hε1 (Int.fract_nonneg ((a : ℝ) * Real.sqrt 2 * 2 ^ q))
    (Int.fract_lt_one _)
  have key : Real.sqrt 2 * (((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ q⌋ + a * 2 ^ q : ℤ) : ℝ) + ε)
      = ((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ q⌋ + a * 2 ^ (q + 1) : ℤ) : ℝ)
        + (Int.fract ((a : ℝ) * Real.sqrt 2 * 2 ^ q) * (1 - Real.sqrt 2) + Real.sqrt 2 * ε) := by
    rw [← Int.self_sub_floor ((a : ℝ) * Real.sqrt 2 * 2 ^ q)]
    push_cast
    linear_combination (a : ℝ) * 2 ^ q * hs2
  rw [key, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨el, eu⟩, add_zero]

/-- **Stoll Theorem 3.2 (induction core).**  Given a positive-index pair `(α, l)`, an offset `ε` in
the universal interval `[1−√2/2, √2/2)`, and the base case at `k = l+2`, the two floor identities
(eqs (5)/(6)) hold for every `k = l + 2 + m`.  The `½`-step is `stollB`/`crux`, the `ε`-step is
`stollA`/`eq8_general`. -/
theorem stoll_pair (a : ℤ) (l : ℕ) {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε)
    (hε1 : ε < Real.sqrt 2 / 2)
    (baseP : (vv ε (2 * (l + 2) - 1) : ℤ)
        = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + a * 2 ^ 1)
    (baseQ : (vv ε (2 * (l + 2)) : ℤ)
        = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + a * 2 ^ 1) :
    ∀ m, (vv ε (2 * (l + 2 + m) - 1) : ℤ) = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ m⌋ + a * 2 ^ (m + 1)
      ∧ (vv ε (2 * (l + 2 + m)) : ℤ) = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (m + 1)⌋ + a * 2 ^ (m + 1) := by
  have hε : 0 ≤ ε := by
    have : (0:ℝ) ≤ 1 - Real.sqrt 2 / 2 := by
      have : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      linarith
    linarith
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using baseP
    · simpa using baseQ
  | succ m ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    set N := l + 2 + m with hN
    -- Q(m) value as a real, for substitution
    have hQr : ((vv ε (2 * N) : ℕ) : ℝ)
        = ((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (m + 1)⌋ + a * 2 ^ (m + 1) : ℤ) : ℝ) := by
      exact_mod_cast ihQ
    -- ε-step: Q(m) ⇒ P(m+1)   (index 2N is even)
    have heven : Even (2 * N) := ⟨N, by ring⟩
    have stepP : (vv ε (2 * N + 1) : ℤ)
        = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (m + 1)⌋ + a * 2 ^ (m + 2) := by
      rw [vv_step_even ε hε (2 * N) heven, hQr]
      have := stollA a (m + 1) hε0 hε1
      simpa using this
    -- P(m+1) value as a real
    have hPr : ((vv ε (2 * N + 1) : ℕ) : ℝ)
        = ((⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (m + 1)⌋ + a * 2 ^ (m + 2) : ℤ) : ℝ) := by
      exact_mod_cast stepP
    -- ½-step: P(m+1) ⇒ Q(m+1)   (index 2N+1 is odd)
    have hodd : ¬ Even (2 * N + 1) := by simp [parity_simps]
    have stepQ : (vv ε (2 * N + 1 + 1) : ℤ)
        = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (m + 2)⌋ + a * 2 ^ (m + 2) := by
      rw [vv_step_odd ε (2 * N + 1) hodd, hPr]
      have := stollB a (m + 1)
      simpa using this
    refine ⟨?_, ?_⟩
    · show (vv ε (2 * (l + 2 + (m + 1)) - 1) : ℤ) = _
      have e : 2 * (l + 2 + (m + 1)) - 1 = 2 * N + 1 := by omega
      rw [e, stepP]
    · show (vv ε (2 * (l + 2 + (m + 1))) : ℤ) = _
      have e : 2 * (l + 2 + (m + 1)) = 2 * N + 1 + 1 := by omega
      rw [e, stepQ]

/-- **Stoll Theorem 3.2 (digit extraction).**  Under the hypotheses of `stoll_pair`, the
Graham–Pollak difference `v_{2k+1} − 2 v_{2k−1}` (with `k = l + 2 + m`) equals the
`(m+1)`-th binary digit of `α√2`.  (The `α·2^…` carry terms cancel exactly.) -/
theorem stoll_digit (a : ℤ) (l : ℕ) {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε)
    (hε1 : ε < Real.sqrt 2 / 2)
    (baseP : (vv ε (2 * (l + 2) - 1) : ℤ) = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + a * 2 ^ 1)
    (baseQ : (vv ε (2 * (l + 2)) : ℤ) = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + a * 2 ^ 1) (m : ℕ) :
    (vv ε (2 * (l + 2 + m) + 1) : ℤ) - 2 * (vv ε (2 * (l + 2 + m) - 1) : ℤ)
      = binDigit ((a : ℝ) * Real.sqrt 2) (m + 1) := by
  have hP1 := (stoll_pair a l hε0 hε1 baseP baseQ (m + 1)).1
  have hP0 := (stoll_pair a l hε0 hε1 baseP baseQ m).1
  -- vv (2*(l+2+m)+1) is P(m+1)'s odd-index value
  have e1 : 2 * (l + 2 + (m + 1)) - 1 = 2 * (l + 2 + m) + 1 := by omega
  rw [e1] at hP1
  rw [hP1, hP0]
  unfold binDigit
  rw [Nat.add_sub_cancel]
  ring

/-! ## Concrete instantiation: Pair 1 (`α = 1`, `l = 0`, `t = √2 − 1`)

Stoll's pair `i = 1`: `ε ∈ [1 − √2/2, √2 − 1)`, `α = 1`, `l = 0`.  Since `α = 1`, the extracted
number is `√2` itself — so a *whole interval* of offsets `ε` (not just `½`) reproduces the binary
digits of `√2`, via `t = √2 − 1 = fract √2`.  This discharges the base case `(vv ε 3, vv ε 4)` from
the recurrence using the `ε`-interval bounds, then applies `stoll_digit`. -/

/-- Base case for pair 1: the recurrence gives `vv ε 3 = 3`, `vv ε 4 = 4` for any
`ε ∈ [1 − √2/2, √2 − 1)`.  (The `ε`-steps `vv 1`, `vv 3` use the interval bounds; the `½`-steps
`vv 2`, `vv 4` are numeric.) -/
private lemma stoll_pair1_base {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε) (hε1 : ε < Real.sqrt 2 - 1) :
    (vv ε 3 : ℤ) = 3 ∧ (vv ε 4 : ℤ) = 4 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hε : 0 ≤ ε := by nlinarith [hε0, hs2, hsnn]
  have e0 : ((vv ε 0 : ℕ) : ℝ) = 1 := by simp [vv]
  -- vv 1 = 1
  have h1 : (vv ε 1 : ℤ) = 1 := by
    rw [show (1:ℕ) = 0 + 1 from rfl, vv_step_even ε hε 0 (by decide), e0, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hε1, hε, hs1, hs2, hspos]
  have e1 : ((vv ε 1 : ℕ) : ℝ) = 1 := by exact_mod_cast h1
  -- vv 2 = 2
  have h2 : (vv ε 2 : ℤ) = 2 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, vv_step_odd ε 1 (by decide), e1, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hs1, hs2, hspos]
  have e2 : ((vv ε 2 : ℕ) : ℝ) = 2 := by exact_mod_cast h2
  -- vv 3 = 3
  have h3 : (vv ε 3 : ℤ) = 3 := by
    rw [show (3:ℕ) = 2 + 1 from rfl, vv_step_even ε hε 2 (by decide), e2, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hε1, hε0, hs1, hs2, hspos]
  have e3 : ((vv ε 3 : ℕ) : ℝ) = 3 := by exact_mod_cast h3
  -- vv 4 = 4
  have h4 : (vv ε 4 : ℤ) = 4 := by
    rw [show (4:ℕ) = 3 + 1 from rfl, vv_step_odd ε 3 (by decide), e3, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hs1, hs2, hspos]
  exact ⟨h3, h4⟩

/-- **Stoll Theorem 3.2, pair 1.**  For every offset `ε ∈ [1 − √2/2, √2 − 1)` and every `m`,
`v_{2k+1} − 2 v_{2k−1}` (with `k = m + 2`) equals the `(m+1)`-th binary digit of `√2`.  A whole
interval of offsets reproduces the binary expansion of `√2` (cf. Stoll's Remark (b)). -/
theorem stoll_pair1 {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε) (hε1 : ε < Real.sqrt 2 - 1) (m : ℕ) :
    (vv ε (2 * (m + 2) + 1) : ℤ) - 2 * (vv ε (2 * (m + 2) - 1) : ℤ)
      = binDigit (Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- the pair-1 interval sits inside the universal interval
  have hε1' : ε < Real.sqrt 2 / 2 := by nlinarith [hε1, hs2, hsnn]
  obtain ⟨hb3, hb4⟩ := stoll_pair1_base hε0 hε1
  have baseP : (vv ε (2 * (0 + 2) - 1) : ℤ)
      = ⌊((1 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (1 : ℤ) * 2 ^ 1 := by
    have hf : ⌊((1 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ = 1 := by
      have he : ((1 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = Real.sqrt 2 := by push_cast; ring
      rw [he, Int.floor_eq_iff]
      constructor <;> push_cast <;> nlinarith [hs2, hsnn]
    rw [show (2 * (0 + 2) - 1 : ℕ) = 3 from rfl, hf, hb3]; norm_num
  have baseQ : (vv ε (2 * (0 + 2)) : ℤ)
      = ⌊((1 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (1 : ℤ) * 2 ^ 1 := by
    have hf : ⌊((1 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ = 2 := by
      have he : ((1 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = Real.sqrt 2 * 2 := by push_cast; ring
      rw [he, Int.floor_eq_iff]
      constructor <;> push_cast <;> nlinarith [hs2, hsnn]
    rw [show (2 * (0 + 2) : ℕ) = 4 from rfl, hf, hb4]; norm_num
  have key := stoll_digit 1 0 hε0 hε1' baseP baseQ m
  have i1 : 2 * (0 + 2 + m) + 1 = 2 * (m + 2) + 1 := by ring
  have i2 : 2 * (0 + 2 + m) - 1 = 2 * (m + 2) - 1 := by omega
  rw [i1, i2] at key
  simpa using key

end Erdos482
