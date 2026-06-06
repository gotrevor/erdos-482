import Erdos482.Basic
import Erdos482.Crux
import Erdos482.Induction
import Erdos482.Digits
import Erdos482.Main

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

/-- Base-case helper: an `ε`-step (even index) lands on the integer `W` when the floor bounds hold.
Reduces a base-case recurrence step to two inequalities (typically `nlinarith` with `√2`/`ε` bounds). -/
private lemma vv_even_to (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (hn : Even n) {V W : ℤ}
    (hV : (vv ε n : ℤ) = V) (hlo : (W : ℝ) ≤ Real.sqrt 2 * ((V : ℝ) + ε))
    (hhi : Real.sqrt 2 * ((V : ℝ) + ε) < (W : ℝ) + 1) : (vv ε (n + 1) : ℤ) = W := by
  rw [vv_step_even ε hε n hn, show ((vv ε n : ℕ) : ℝ) = (V : ℝ) by exact_mod_cast hV,
    Int.floor_eq_iff]
  exact ⟨hlo, hhi⟩

/-- Base-case helper: a `½`-step (odd index) lands on the integer `W` when the floor bounds hold. -/
private lemma vv_odd_to (ε : ℝ) (n : ℕ) (hn : ¬ Even n) {V W : ℤ}
    (hV : (vv ε n : ℤ) = V) (hlo : (W : ℝ) ≤ Real.sqrt 2 * ((V : ℝ) + 1 / 2))
    (hhi : Real.sqrt 2 * ((V : ℝ) + 1 / 2) < (W : ℝ) + 1) : (vv ε (n + 1) : ℤ) = W := by
  rw [vv_step_odd ε n hn, show ((vv ε n : ℕ) : ℝ) = (V : ℝ) by exact_mod_cast hV, Int.floor_eq_iff]
  exact ⟨hlo, hhi⟩

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

/-! ## Faithful `t_i` framing: digits of `(α√2 − β)/2^l` = digits of `α√2`, shifted by `l` -/

/-- For `m ≥ l`, `⌊((α√2 − β)/2^l)·2^m⌋ = ⌊α√2·2^(m−l)⌋ − β·2^(m−l)` (the integer `β·2^(m−l)`
factors out of the floor). -/
private lemma floor_t_pow (a b : ℤ) (l m : ℕ) (hm : l ≤ m) :
    ⌊((a : ℝ) * Real.sqrt 2 - (b : ℝ)) / 2 ^ l * 2 ^ m⌋
      = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (m - l)⌋ - b * 2 ^ (m - l) := by
  have hpow : (2:ℝ) ^ m = 2 ^ l * 2 ^ (m - l) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hne : (2:ℝ) ^ l ≠ 0 := by positivity
  have e : ((a : ℝ) * Real.sqrt 2 - (b : ℝ)) / 2 ^ l * 2 ^ m
      = (a : ℝ) * Real.sqrt 2 * 2 ^ (m - l) - ((b * 2 ^ (m - l) : ℤ) : ℝ) := by
    rw [hpow]; field_simp; push_cast; ring
  rw [e, Int.floor_sub_intCast]

/-- **Theorem 3.2, faithful `t_i` form.**  The `j`-th binary digit of `α√2` equals the `(j+l)`-th
binary digit of `t = (α√2 − β)/2^l`.  Combined with `stoll_digit`, this restates each pair's
conclusion in terms of the paper's `t_i = (α_i√2 − β_i)/2^{l_i}` (e.g. pair 6's
`t_6 = (759250125√2 − 314491699)/2^29`). -/
theorem binDigit_div_pow (a b : ℤ) (l j : ℕ) (hj : 1 ≤ j) :
    binDigit (((a : ℝ) * Real.sqrt 2 - (b : ℝ)) / 2 ^ l) (j + l)
      = binDigit ((a : ℝ) * Real.sqrt 2) j := by
  unfold binDigit
  have h1 : ⌊((a : ℝ) * Real.sqrt 2 - (b : ℝ)) / 2 ^ l * 2 ^ (j + l)⌋
      = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ j⌋ - b * 2 ^ j := by
    have := floor_t_pow a b l (j + l) (Nat.le_add_left l j)
    simpa [Nat.add_sub_cancel] using this
  have h2 : ⌊((a : ℝ) * Real.sqrt 2 - (b : ℝ)) / 2 ^ l * 2 ^ (j + l - 1)⌋
      = ⌊(a : ℝ) * Real.sqrt 2 * 2 ^ (j - 1)⌋ - b * 2 ^ (j - 1) := by
    have := floor_t_pow a b l (j + l - 1) (by omega)
    simpa [show j + l - 1 - l = j - 1 from by omega] using this
  rw [h1, h2]
  have hp : (2 : ℤ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hj]
  rw [hp]; ring

/-! ## Floor of `c√2` via exact integer inequalities (no decimal approximation) -/

/-- `⌊c√2⌋ = d` whenever `d² ≤ 2c²` and `2c² < (d+1)²` (with `0 < c`).  Both hypotheses are exact
integer comparisons closed by `norm_num`, so this pins `⌊c√2⌋` for arbitrarily large `c` without any
decimal bound on `√2`. -/
private lemma floor_mul_sqrt2 (c d : ℕ) (hc : 0 < c) (h1 : (d : ℤ) ^ 2 ≤ 2 * (c : ℤ) ^ 2)
    (h2 : 2 * (c : ℤ) ^ 2 < ((d : ℤ) + 1) ^ 2) :
    ⌊(c : ℝ) * Real.sqrt 2⌋ = d := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcr : (0:ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h1r : (d : ℝ) ^ 2 ≤ 2 * (c : ℝ) ^ 2 := by exact_mod_cast h1
  have h2r : 2 * (c : ℝ) ^ 2 < ((d : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast
    nlinarith [h1r, hs2, hsnn, mul_pos hcr hspos, sq_nonneg ((c : ℝ) * Real.sqrt 2 - d)]
  · push_cast
    nlinarith [h2r, hs2, hsnn, mul_pos hcr hspos, sq_nonneg ((c : ℝ) * Real.sqrt 2 + d + 1)]

/-! ## Rational enclosures of `√2` and `ε = 1 − π²/e³` (for the unconditional Cor 3.3) -/

/-- `√2` lower bound to 13 digits, via `Real.lt_sqrt` (reduces to an exact rational square). -/
private lemma sqrt2_lo : (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- `√2` upper bound to 13 digits, via `Real.sqrt_lt'`. -/
private lemma sqrt2_hi : Real.sqrt 2 < (14142135623731 / 10000000000000 : ℝ) :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- `0.50862 ≤ 1 − π²/e³`, from `π < 3.141593` and `e > 2.7182818283` (`pi_lt_d6`, `exp_one_gt_d9`). -/
private lemma cor33_eps_lo : (25431 / 50000 : ℝ) ≤ 1 - Real.pi ^ 2 / Real.exp 3 := by
  have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have he3pos : (0:ℝ) < Real.exp 3 := Real.exp_pos 3
  have h1 : Real.pi ^ 2 ≤ (3.141593:ℝ) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt Real.pi_pos) (le_of_lt Real.pi_lt_d6) 2
  have h2 : (2.7182818283:ℝ) ^ 3 ≤ Real.exp 3 := by
    rw [he3]; exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 3
  have key : Real.pi ^ 2 ≤ (1 - 50862 / 100000) * Real.exp 3 := by nlinarith [h1, h2]
  have hdiv : Real.pi ^ 2 / Real.exp 3 ≤ 1 - 50862 / 100000 := by
    rw [div_le_iff₀ he3pos]; linarith [key]
  linarith [hdiv]

/-- `1 − π²/e³ ≤ 0.508622`, from `π > 3.141592` and `e < 2.7182818286` (`pi_gt_d6`, `exp_one_lt_d9`). -/
private lemma cor33_eps_hi : 1 - Real.pi ^ 2 / Real.exp 3 ≤ (254311 / 500000 : ℝ) := by
  have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have he3pos : (0:ℝ) < Real.exp 3 := Real.exp_pos 3
  have h1 : (3.141592:ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.pi_gt_d6) 2
  have h2 : Real.exp 3 ≤ (2.7182818286:ℝ) ^ 3 := by
    rw [he3]; exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 3
  have key : (1 - 508622 / 1000000) * Real.exp 3 ≤ Real.pi ^ 2 := by nlinarith [h1, h2]
  have hdiv : (1 - 508622 / 1000000 : ℝ) ≤ Real.pi ^ 2 / Real.exp 3 := by
    rw [le_div_iff₀ he3pos]; linarith [key]
  linarith [hdiv]

set_option maxHeartbeats 1000000 in
/-- **Corollary 3.3 base case, from rational bounds.**  Given `√2` pinned to a 13-digit
rational interval and `ε ∈ [0.50862, 0.508622]` (both satisfied by `ε = 1 − π²/e³`), the 62-step
recurrence determines `vv ε 61 = 2592242074`, `vv ε 62 = 3665983898` (the values feeding `cor33`).
Each step reduces — after `mul_add` — to `linarith` over the √2/ε bounds plus the two product
bounds `hpl`/`hph`.  Script-generated (62 floor steps); worst floor margin ≈ 0.0024. -/
private lemma cor33_base_of_bounds {ε : ℝ}
    (hs2lo : (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2) (hs2hi : Real.sqrt 2 < (14142135623731 / 10000000000000 : ℝ))
    (hεlo : (25431 / 50000 : ℝ) ≤ ε) (hεhi : ε ≤ (254311 / 500000 : ℝ)) :
    (vv ε 61 : ℤ) = 2592242074 ∧ (vv ε 62 : ℤ) = 3665983898 := by
  have hεpos : (0:ℝ) ≤ ε := by linarith
  have hpl : Real.sqrt 2 * ε ≥ (1414213562373 / 1000000000000 : ℝ) * (25431 / 50000 : ℝ) := by nlinarith [hs2lo, hεlo, hεpos]
  have hph : Real.sqrt 2 * ε ≤ (14142135623731 / 10000000000000 : ℝ) * (254311 / 500000 : ℝ) := by nlinarith [hs2hi, hεhi, hεpos]
  have v0 : (vv ε 0 : ℤ) = 1 := by simp [vv]
  have v1 : (vv ε 1 : ℤ) = 2 := vv_even_to ε hεpos 0 (by decide) v0
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v2 : (vv ε 2 : ℤ) = 3 := vv_odd_to ε 1 (by decide) v1
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v3 : (vv ε 3 : ℤ) = 4 := vv_even_to ε hεpos 2 (by decide) v2
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v4 : (vv ε 4 : ℤ) = 6 := vv_odd_to ε 3 (by decide) v3
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v5 : (vv ε 5 : ℤ) = 9 := vv_even_to ε hεpos 4 (by decide) v4
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v6 : (vv ε 6 : ℤ) = 13 := vv_odd_to ε 5 (by decide) v5
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v7 : (vv ε 7 : ℤ) = 19 := vv_even_to ε hεpos 6 (by decide) v6
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v8 : (vv ε 8 : ℤ) = 27 := vv_odd_to ε 7 (by decide) v7
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v9 : (vv ε 9 : ℤ) = 38 := vv_even_to ε hεpos 8 (by decide) v8
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v10 : (vv ε 10 : ℤ) = 54 := vv_odd_to ε 9 (by decide) v9
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v11 : (vv ε 11 : ℤ) = 77 := vv_even_to ε hεpos 10 (by decide) v10
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v12 : (vv ε 12 : ℤ) = 109 := vv_odd_to ε 11 (by decide) v11
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v13 : (vv ε 13 : ℤ) = 154 := vv_even_to ε hεpos 12 (by decide) v12
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v14 : (vv ε 14 : ℤ) = 218 := vv_odd_to ε 13 (by decide) v13
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v15 : (vv ε 15 : ℤ) = 309 := vv_even_to ε hεpos 14 (by decide) v14
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v16 : (vv ε 16 : ℤ) = 437 := vv_odd_to ε 15 (by decide) v15
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v17 : (vv ε 17 : ℤ) = 618 := vv_even_to ε hεpos 16 (by decide) v16
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v18 : (vv ε 18 : ℤ) = 874 := vv_odd_to ε 17 (by decide) v17
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v19 : (vv ε 19 : ℤ) = 1236 := vv_even_to ε hεpos 18 (by decide) v18
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v20 : (vv ε 20 : ℤ) = 1748 := vv_odd_to ε 19 (by decide) v19
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v21 : (vv ε 21 : ℤ) = 2472 := vv_even_to ε hεpos 20 (by decide) v20
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v22 : (vv ε 22 : ℤ) = 3496 := vv_odd_to ε 21 (by decide) v21
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v23 : (vv ε 23 : ℤ) = 4944 := vv_even_to ε hεpos 22 (by decide) v22
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v24 : (vv ε 24 : ℤ) = 6992 := vv_odd_to ε 23 (by decide) v23
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v25 : (vv ε 25 : ℤ) = 9888 := vv_even_to ε hεpos 24 (by decide) v24
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v26 : (vv ε 26 : ℤ) = 13984 := vv_odd_to ε 25 (by decide) v25
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v27 : (vv ε 27 : ℤ) = 19777 := vv_even_to ε hεpos 26 (by decide) v26
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v28 : (vv ε 28 : ℤ) = 27969 := vv_odd_to ε 27 (by decide) v27
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v29 : (vv ε 29 : ℤ) = 39554 := vv_even_to ε hεpos 28 (by decide) v28
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v30 : (vv ε 30 : ℤ) = 55938 := vv_odd_to ε 29 (by decide) v29
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v31 : (vv ε 31 : ℤ) = 79108 := vv_even_to ε hεpos 30 (by decide) v30
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v32 : (vv ε 32 : ℤ) = 111876 := vv_odd_to ε 31 (by decide) v31
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v33 : (vv ε 33 : ℤ) = 158217 := vv_even_to ε hεpos 32 (by decide) v32
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v34 : (vv ε 34 : ℤ) = 223753 := vv_odd_to ε 33 (by decide) v33
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v35 : (vv ε 35 : ℤ) = 316435 := vv_even_to ε hεpos 34 (by decide) v34
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v36 : (vv ε 36 : ℤ) = 447507 := vv_odd_to ε 35 (by decide) v35
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v37 : (vv ε 37 : ℤ) = 632871 := vv_even_to ε hεpos 36 (by decide) v36
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v38 : (vv ε 38 : ℤ) = 895015 := vv_odd_to ε 37 (by decide) v37
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v39 : (vv ε 39 : ℤ) = 1265743 := vv_even_to ε hεpos 38 (by decide) v38
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v40 : (vv ε 40 : ℤ) = 1790031 := vv_odd_to ε 39 (by decide) v39
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v41 : (vv ε 41 : ℤ) = 2531486 := vv_even_to ε hεpos 40 (by decide) v40
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v42 : (vv ε 42 : ℤ) = 3580062 := vv_odd_to ε 41 (by decide) v41
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v43 : (vv ε 43 : ℤ) = 5062972 := vv_even_to ε hεpos 42 (by decide) v42
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v44 : (vv ε 44 : ℤ) = 7160124 := vv_odd_to ε 43 (by decide) v43
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v45 : (vv ε 45 : ℤ) = 10125945 := vv_even_to ε hεpos 44 (by decide) v44
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v46 : (vv ε 46 : ℤ) = 14320249 := vv_odd_to ε 45 (by decide) v45
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v47 : (vv ε 47 : ℤ) = 20251891 := vv_even_to ε hεpos 46 (by decide) v46
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v48 : (vv ε 48 : ℤ) = 28640499 := vv_odd_to ε 47 (by decide) v47
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v49 : (vv ε 49 : ℤ) = 40503782 := vv_even_to ε hεpos 48 (by decide) v48
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v50 : (vv ε 50 : ℤ) = 57280998 := vv_odd_to ε 49 (by decide) v49
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v51 : (vv ε 51 : ℤ) = 81007564 := vv_even_to ε hεpos 50 (by decide) v50
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v52 : (vv ε 52 : ℤ) = 114561996 := vv_odd_to ε 51 (by decide) v51
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v53 : (vv ε 53 : ℤ) = 162015129 := vv_even_to ε hεpos 52 (by decide) v52
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v54 : (vv ε 54 : ℤ) = 229123993 := vv_odd_to ε 53 (by decide) v53
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v55 : (vv ε 55 : ℤ) = 324030259 := vv_even_to ε hεpos 54 (by decide) v54
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v56 : (vv ε 56 : ℤ) = 458247987 := vv_odd_to ε 55 (by decide) v55
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v57 : (vv ε 57 : ℤ) = 648060518 := vv_even_to ε hεpos 56 (by decide) v56
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v58 : (vv ε 58 : ℤ) = 916495974 := vv_odd_to ε 57 (by decide) v57
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v59 : (vv ε 59 : ℤ) = 1296121037 := vv_even_to ε hεpos 58 (by decide) v58
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v60 : (vv ε 60 : ℤ) = 1832991949 := vv_odd_to ε 59 (by decide) v59
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v61 : (vv ε 61 : ℤ) = 2592242074 := vv_even_to ε hεpos 60 (by decide) v60
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v62 : (vv ε 62 : ℤ) = 3665983898 := vv_odd_to ε 61 (by decide) v61
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  exact ⟨v61, v62⟩


/-! ## Corollary 3.3 — the binary digits of `759250125·√2`

Stoll's headline corollary: with `α = 759250125`, `l = 29`, and `ε = 1 − π²/e³` (which lies in pair
6's interval — see `tools/aristotle/cor33mem`), the Graham–Pollak difference `v_{2k+1} − 2 v_{2k−1}`
reads off the binary digits of `759250125·√2`.

The `ε`-sensitive base case (`vv ε 61 = 2592242074`, `vv ε 62 = 3665983898`, where
`⌊759250125·√2⌋ = 2³⁰` and `⌊1518500250·√2⌋ = 2³¹`) is a finite 62-step recurrence computation that
holds exactly for `ε` in pair 6's tight interval `[0.5012400…, 0.5103528…)`; it is supplied here as a
hypothesis (the only remaining obligation for an unconditional Cor 3.3 — see `PENDING_WORK.md`).
Everything downstream is the axiom-clean general core. -/
theorem cor33 {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε) (hε1 : ε < Real.sqrt 2 / 2)
    (base61 : (vv ε 61 : ℤ) = 2592242074) (base62 : (vv ε 62 : ℤ) = 3665983898) (m : ℕ) :
    (vv ε (2 * (m + 31) + 1) : ℤ) - 2 * (vv ε (2 * (m + 31) - 1) : ℤ)
      = binDigit (759250125 * Real.sqrt 2) (m + 1) := by
  have hf1 : ⌊(759250125 : ℝ) * Real.sqrt 2⌋ = 1073741824 :=
    floor_mul_sqrt2 759250125 1073741824 (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊(1518500250 : ℝ) * Real.sqrt 2⌋ = 2147483648 :=
    floor_mul_sqrt2 1518500250 2147483648 (by norm_num) (by norm_num) (by norm_num)
  have baseP : (vv ε (2 * (29 + 2) - 1) : ℤ)
      = ⌊((759250125 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (759250125 : ℤ) * 2 ^ 1 := by
    have he : ((759250125 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = (759250125 : ℝ) * Real.sqrt 2 := by
      push_cast; ring
    rw [show (2 * (29 + 2) - 1 : ℕ) = 61 from rfl, he, hf1, base61]; norm_num
  have baseQ : (vv ε (2 * (29 + 2)) : ℤ)
      = ⌊((759250125 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (759250125 : ℤ) * 2 ^ 1 := by
    have he : ((759250125 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = (1518500250 : ℝ) * Real.sqrt 2 := by
      push_cast; ring
    rw [show (2 * (29 + 2) : ℕ) = 62 from rfl, he, hf2, base62]; norm_num
  have key := stoll_digit 759250125 29 hε0 hε1 baseP baseQ m
  have i1 : 2 * (29 + 2 + m) + 1 = 2 * (m + 31) + 1 := by ring
  have i2 : 2 * (29 + 2 + m) - 1 = 2 * (m + 31) - 1 := by omega
  rw [i1, i2] at key
  simpa using key

/-- **Corollary 3.3, UNCONDITIONAL.**  For the sequence `w` of the paper (`ε = 1 − π²/e³`,
`w_{n+1} = ⌊√2(wₙ + ε)⌋` on odd `n`, `⌊√2(wₙ + ½)⌋` on even `n`), and every `m`,
`w_{2k+1} − 2 w_{2k−1}` (with `k = m + 31`) equals the `(m+1)`-th binary digit of `759250125·√2`.

This is Stoll's title result with **no remaining hypotheses**: the `ε`-sensitive 62-step base case is
discharged by `cor33_base_of_bounds` from the rational enclosures `sqrt2_lo`/`sqrt2_hi` and
`cor33_eps_lo`/`cor33_eps_hi` (`ε ∈ [0.50862, 0.508622]`, proved from mathlib's `π`/`e` bounds). -/
theorem cor33_unconditional (m : ℕ) :
    (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) + 1) : ℤ)
        - 2 * (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) - 1) : ℤ)
      = binDigit (759250125 * Real.sqrt 2) (m + 1) := by
  have hslo := sqrt2_lo
  have hshi := sqrt2_hi
  have hεlo := cor33_eps_lo
  have hεhi := cor33_eps_hi
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ 1 - Real.pi ^ 2 / Real.exp 3 := by
    nlinarith [hεlo, hs2, hsnn]
  have hε1 : 1 - Real.pi ^ 2 / Real.exp 3 < Real.sqrt 2 / 2 := by linarith [hεhi, hslo]
  obtain ⟨b61, b62⟩ := cor33_base_of_bounds hslo hshi hεlo hεhi
  exact cor33 hε0 hε1 b61 b62 m

/-! ## Concrete instantiation: Pair 8 (`α = 3`, `l = 1`, `t = (3√2 − 1)/2`)

Stoll's pair `i = 8`: `ε ∈ [(5/2)√2 − 3, √2/2)`, `α = 3`, `l = 1`, so `v_{2k+1} − 2 v_{2k−1}`
reads off the binary digits of `3√2`.  Base case: the recurrence gives
`vv ε 0..6 = 1,2,3,5,7,10,14`, stable across the whole interval. -/

/-- Base case for pair 8: `vv ε 5 = 10`, `vv ε 6 = 14` for `ε ∈ [(5/2)√2 − 3, √2/2)`. -/
private lemma stoll_pair8_base {ε : ℝ} (hlo : 5 / 2 * Real.sqrt 2 - 3 ≤ ε)
    (hhi : ε < Real.sqrt 2 / 2) :
    (vv ε 5 : ℤ) = 10 ∧ (vv ε 6 : ℤ) = 14 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hε : 0 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have e0 : ((vv ε 0 : ℕ) : ℝ) = 1 := by simp [vv]
  have h1 : (vv ε 1 : ℤ) = 2 := by
    rw [show (1:ℕ) = 0 + 1 from rfl, vv_step_even ε hε 0 (by decide), e0, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hlo, hhi, hs1, hs2, hspos]
  have e1 : ((vv ε 1 : ℕ) : ℝ) = 2 := by exact_mod_cast h1
  have h2 : (vv ε 2 : ℤ) = 3 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, vv_step_odd ε 1 (by decide), e1, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hs1, hs2, hspos]
  have e2 : ((vv ε 2 : ℕ) : ℝ) = 3 := by exact_mod_cast h2
  have h3 : (vv ε 3 : ℤ) = 5 := by
    rw [show (3:ℕ) = 2 + 1 from rfl, vv_step_even ε hε 2 (by decide), e2, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hlo, hhi, hs1, hs2, hspos]
  have e3 : ((vv ε 3 : ℕ) : ℝ) = 5 := by exact_mod_cast h3
  have h4 : (vv ε 4 : ℤ) = 7 := by
    rw [show (4:ℕ) = 3 + 1 from rfl, vv_step_odd ε 3 (by decide), e3, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hs1, hs2, hspos]
  have e4 : ((vv ε 4 : ℕ) : ℝ) = 7 := by exact_mod_cast h4
  have h5 : (vv ε 5 : ℤ) = 10 := by
    rw [show (5:ℕ) = 4 + 1 from rfl, vv_step_even ε hε 4 (by decide), e4, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hlo, hhi, hs1, hs2, hspos]
  have e5 : ((vv ε 5 : ℕ) : ℝ) = 10 := by exact_mod_cast h5
  have h6 : (vv ε 6 : ℤ) = 14 := by
    rw [show (6:ℕ) = 5 + 1 from rfl, vv_step_odd ε 5 (by decide), e5, Int.floor_eq_iff]
    constructor <;> push_cast <;> nlinarith [hs1, hs2, hspos]
  exact ⟨h5, h6⟩

/-- **Stoll Theorem 3.2, pair 8.**  For every offset `ε ∈ [(5/2)√2 − 3, √2/2)` and every `m`,
`v_{2k+1} − 2 v_{2k−1}` (with `k = m + 3`) equals the `(m+1)`-th binary digit of `3√2`. -/
theorem stoll_pair8 {ε : ℝ} (hlo : 5 / 2 * Real.sqrt 2 - 3 ≤ ε) (hhi : ε < Real.sqrt 2 / 2)
    (m : ℕ) :
    (vv ε (2 * (m + 3) + 1) : ℤ) - 2 * (vv ε (2 * (m + 3) - 1) : ℤ)
      = binDigit (3 * Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  obtain ⟨hb5, hb6⟩ := stoll_pair8_base hlo hhi
  have baseP : (vv ε (2 * (1 + 2) - 1) : ℤ)
      = ⌊((3 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (3 : ℤ) * 2 ^ 1 := by
    have hf : ⌊((3 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ = 4 := by
      have he : ((3 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = 3 * Real.sqrt 2 := by push_cast; ring
      rw [he, Int.floor_eq_iff]
      constructor <;> push_cast <;> nlinarith [hs2, hsnn]
    rw [show (2 * (1 + 2) - 1 : ℕ) = 5 from rfl, hf, hb5]; norm_num
  have baseQ : (vv ε (2 * (1 + 2)) : ℤ)
      = ⌊((3 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (3 : ℤ) * 2 ^ 1 := by
    have hf : ⌊((3 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ = 8 := by
      have he : ((3 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = 6 * Real.sqrt 2 := by push_cast; ring
      rw [he, Int.floor_eq_iff]
      constructor <;> push_cast <;> nlinarith [hs2, hsnn]
    rw [show (2 * (1 + 2) : ℕ) = 6 from rfl, hf, hb6]; norm_num
  have key := stoll_digit 3 1 hε0 hhi baseP baseQ m
  have i1 : 2 * (1 + 2 + m) + 1 = 2 * (m + 3) + 1 := by ring
  have i2 : 2 * (1 + 2 + m) - 1 = 2 * (m + 3) - 1 := by omega
  rw [i1, i2] at key
  simpa using key

/-! ## Concrete instantiation: Pair 2 (`α = 11`, `l = 3`, `t = (11√2 − 5)/8`)

Stoll's pair `i = 2`: `ε ∈ [√2 − 1, (19/2)√2 − 13)`, `α = 11`, `l = 3`, so the difference reads off
the binary digits of `11√2`.  Base case `vv ε 0..10 = 1,2,3,4,6,9,13,18,26,37,53` (the `vv_even_to`/
`vv_odd_to` helpers reduce each step to two `nlinarith` bounds). -/

/-- Base case for pair 2: `vv ε 9 = 37`, `vv ε 10 = 53` for `ε ∈ [√2 − 1, (19/2)√2 − 13)`. -/
private lemma stoll_pair2_base {ε : ℝ} (hlo : Real.sqrt 2 - 1 ≤ ε)
    (hhi : ε < 19 / 2 * Real.sqrt 2 - 13) :
    (vv ε 9 : ℤ) = 37 ∧ (vv ε 10 : ℤ) = 53 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hε : 0 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have v0 : (vv ε 0 : ℤ) = 1 := by simp [vv]
  have v1 : (vv ε 1 : ℤ) = 2 := vv_even_to ε hε 0 (by decide) v0
    (by push_cast; nlinarith [hlo, hs1, hs2, hspos]) (by push_cast; nlinarith [hhi, hs1, hs2, hspos])
  have v2 : (vv ε 2 : ℤ) = 3 := vv_odd_to ε 1 (by decide) v1
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v3 : (vv ε 3 : ℤ) = 4 := vv_even_to ε hε 2 (by decide) v2
    (by push_cast; nlinarith [hlo, hs1, hs2, hspos]) (by push_cast; nlinarith [hhi, hs1, hs2, hspos])
  have v4 : (vv ε 4 : ℤ) = 6 := vv_odd_to ε 3 (by decide) v3
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v5 : (vv ε 5 : ℤ) = 9 := vv_even_to ε hε 4 (by decide) v4
    (by push_cast; nlinarith [hlo, hs1, hs2, hspos]) (by push_cast; nlinarith [hhi, hs1, hs2, hspos])
  have v6 : (vv ε 6 : ℤ) = 13 := vv_odd_to ε 5 (by decide) v5
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v7 : (vv ε 7 : ℤ) = 18 := vv_even_to ε hε 6 (by decide) v6
    (by push_cast; nlinarith [hlo, hs1, hs2, hspos]) (by push_cast; nlinarith [hhi, hs1, hs2, hspos])
  have v8 : (vv ε 8 : ℤ) = 26 := vv_odd_to ε 7 (by decide) v7
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v9 : (vv ε 9 : ℤ) = 37 := vv_even_to ε hε 8 (by decide) v8
    (by push_cast; nlinarith [hlo, hs1, hs2, hspos]) (by push_cast; nlinarith [hhi, hs1, hs2, hspos])
  have v10 : (vv ε 10 : ℤ) = 53 := vv_odd_to ε 9 (by decide) v9
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  exact ⟨v9, v10⟩

/-- **Stoll Theorem 3.2, pair 2.**  For every offset `ε ∈ [√2 − 1, (19/2)√2 − 13)` and every `m`,
`v_{2k+1} − 2 v_{2k−1}` (with `k = m + 5`) equals the `(m+1)`-th binary digit of `11√2`. -/
theorem stoll_pair2 {ε : ℝ} (hlo : Real.sqrt 2 - 1 ≤ ε) (hhi : ε < 19 / 2 * Real.sqrt 2 - 13)
    (m : ℕ) :
    (vv ε (2 * (m + 5) + 1) : ℤ) - 2 * (vv ε (2 * (m + 5) - 1) : ℤ)
      = binDigit (11 * Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have hε1 : ε < Real.sqrt 2 / 2 := by nlinarith [hhi, hs2, hsnn]
  obtain ⟨hb9, hb10⟩ := stoll_pair2_base hlo hhi
  have baseP : (vv ε (2 * (3 + 2) - 1) : ℤ)
      = ⌊((11 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (11 : ℤ) * 2 ^ 1 := by
    have hf : ⌊((11 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ = 15 := by
      have he : ((11 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = 11 * Real.sqrt 2 := by push_cast; ring
      rw [he, Int.floor_eq_iff]
      constructor <;> push_cast <;> nlinarith [hs2, hsnn]
    rw [show (2 * (3 + 2) - 1 : ℕ) = 9 from rfl, hf, hb9]; norm_num
  have baseQ : (vv ε (2 * (3 + 2)) : ℤ)
      = ⌊((11 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (11 : ℤ) * 2 ^ 1 := by
    have hf : ⌊((11 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ = 31 := by
      have he : ((11 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = 22 * Real.sqrt 2 := by push_cast; ring
      rw [he, Int.floor_eq_iff]
      constructor <;> push_cast <;> nlinarith [hs2, hsnn]
    rw [show (2 * (3 + 2) : ℕ) = 10 from rfl, hf, hb10]; norm_num
  have key := stoll_digit 11 3 hε0 hε1 baseP baseQ m
  have i1 : 2 * (3 + 2 + m) + 1 = 2 * (m + 5) + 1 := by ring
  have i2 : 2 * (3 + 2 + m) - 1 = 2 * (m + 5) - 1 := by omega
  rw [i1, i2] at key
  simpa using key

set_option maxHeartbeats 800000 in
/-- Base case for pair 3 (α=45, l=5): `vv ε 13 = 153`, `vv ε 14 = 217` for
`ε ∈ [19 / 2 * √2 - 13, 77 / 2 * √2 - 54)`. -/
private lemma stoll_pair3_base {ε : ℝ} (hlo : 19 / 2 * Real.sqrt 2 - 13 ≤ ε) (hhi : ε < 77 / 2 * Real.sqrt 2 - 54) :
    (vv ε 13 : ℤ) = 153 ∧ (vv ε 14 : ℤ) = 217 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hε : 0 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have v0 : (vv ε 0 : ℤ) = 1 := by simp [vv]
  have v1 : (vv ε 1 : ℤ) = 2 := vv_even_to ε hε 0 (by decide) v0
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v2 : (vv ε 2 : ℤ) = 3 := vv_odd_to ε 1 (by decide) v1
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v3 : (vv ε 3 : ℤ) = 4 := vv_even_to ε hε 2 (by decide) v2
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v4 : (vv ε 4 : ℤ) = 6 := vv_odd_to ε 3 (by decide) v3
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v5 : (vv ε 5 : ℤ) = 9 := vv_even_to ε hε 4 (by decide) v4
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v6 : (vv ε 6 : ℤ) = 13 := vv_odd_to ε 5 (by decide) v5
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v7 : (vv ε 7 : ℤ) = 19 := vv_even_to ε hε 6 (by decide) v6
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v8 : (vv ε 8 : ℤ) = 27 := vv_odd_to ε 7 (by decide) v7
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v9 : (vv ε 9 : ℤ) = 38 := vv_even_to ε hε 8 (by decide) v8
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v10 : (vv ε 10 : ℤ) = 54 := vv_odd_to ε 9 (by decide) v9
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v11 : (vv ε 11 : ℤ) = 76 := vv_even_to ε hε 10 (by decide) v10
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v12 : (vv ε 12 : ℤ) = 108 := vv_odd_to ε 11 (by decide) v11
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v13 : (vv ε 13 : ℤ) = 153 := vv_even_to ε hε 12 (by decide) v12
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v14 : (vv ε 14 : ℤ) = 217 := vv_odd_to ε 13 (by decide) v13
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  exact ⟨v13, v14⟩
/-- **Stoll Theorem 3.2, pair 3.**  For `ε ∈ [19 / 2 * √2 - 13, 77 / 2 * √2 - 54)`,
`v_{2k+1} − 2 v_{2k−1}` (k=m+7) is the (m+1)-th binary digit of `45√2`. -/
theorem stoll_pair3 {ε : ℝ} (hlo : 19 / 2 * Real.sqrt 2 - 13 ≤ ε) (hhi : ε < 77 / 2 * Real.sqrt 2 - 54) (m : ℕ) :
    (vv ε (2 * (m + 7) + 1) : ℤ) - 2 * (vv ε (2 * (m + 7) - 1) : ℤ)
      = binDigit (45 * Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have hε1 : ε < Real.sqrt 2 / 2 := by nlinarith [hhi, hs2, hsnn]
  obtain ⟨hbp, hbq⟩ := stoll_pair3_base hlo hhi
  have hf1 : ⌊(45 : ℝ) * Real.sqrt 2⌋ = 63 :=
    floor_mul_sqrt2 45 63 (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊(90 : ℝ) * Real.sqrt 2⌋ = 127 :=
    floor_mul_sqrt2 90 127 (by norm_num) (by norm_num) (by norm_num)
  have baseP : (vv ε (2 * (5 + 2) - 1) : ℤ) = ⌊((45 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (45 : ℤ) * 2 ^ 1 := by
    have he : ((45 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = (45 : ℝ) * Real.sqrt 2 := by push_cast; ring
    rw [show (2 * (5 + 2) - 1 : ℕ) = 13 from rfl, he, hf1, hbp]; norm_num
  have baseQ : (vv ε (2 * (5 + 2)) : ℤ) = ⌊((45 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (45 : ℤ) * 2 ^ 1 := by
    have he : ((45 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = (90 : ℝ) * Real.sqrt 2 := by push_cast; ring
    rw [show (2 * (5 + 2) : ℕ) = 14 from rfl, he, hf2, hbq]; norm_num
  have key := stoll_digit 45 5 hε0 hε1 baseP baseQ m
  have i1 : 2 * (5 + 2 + m) + 1 = 2 * (m + 7) + 1 := by ring
  have i2 : 2 * (5 + 2 + m) - 1 = 2 * (m + 7) - 1 := by omega
  rw [i1, i2] at key
  simpa using key

set_option maxHeartbeats 800000 in
/-- Base case for pair 4 (α=181, l=7): `vv ε 17 = 617`, `vv ε 18 = 873` for
`ε ∈ [77 / 2 * √2 - 54, 309 / 2 * √2 - 218)`. -/
private lemma stoll_pair4_base {ε : ℝ} (hlo : 77 / 2 * Real.sqrt 2 - 54 ≤ ε) (hhi : ε < 309 / 2 * Real.sqrt 2 - 218) :
    (vv ε 17 : ℤ) = 617 ∧ (vv ε 18 : ℤ) = 873 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hε : 0 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have v0 : (vv ε 0 : ℤ) = 1 := by simp [vv]
  have v1 : (vv ε 1 : ℤ) = 2 := vv_even_to ε hε 0 (by decide) v0
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v2 : (vv ε 2 : ℤ) = 3 := vv_odd_to ε 1 (by decide) v1
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v3 : (vv ε 3 : ℤ) = 4 := vv_even_to ε hε 2 (by decide) v2
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v4 : (vv ε 4 : ℤ) = 6 := vv_odd_to ε 3 (by decide) v3
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v5 : (vv ε 5 : ℤ) = 9 := vv_even_to ε hε 4 (by decide) v4
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v6 : (vv ε 6 : ℤ) = 13 := vv_odd_to ε 5 (by decide) v5
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v7 : (vv ε 7 : ℤ) = 19 := vv_even_to ε hε 6 (by decide) v6
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v8 : (vv ε 8 : ℤ) = 27 := vv_odd_to ε 7 (by decide) v7
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v9 : (vv ε 9 : ℤ) = 38 := vv_even_to ε hε 8 (by decide) v8
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v10 : (vv ε 10 : ℤ) = 54 := vv_odd_to ε 9 (by decide) v9
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v11 : (vv ε 11 : ℤ) = 77 := vv_even_to ε hε 10 (by decide) v10
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v12 : (vv ε 12 : ℤ) = 109 := vv_odd_to ε 11 (by decide) v11
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v13 : (vv ε 13 : ℤ) = 154 := vv_even_to ε hε 12 (by decide) v12
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v14 : (vv ε 14 : ℤ) = 218 := vv_odd_to ε 13 (by decide) v13
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v15 : (vv ε 15 : ℤ) = 308 := vv_even_to ε hε 14 (by decide) v14
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v16 : (vv ε 16 : ℤ) = 436 := vv_odd_to ε 15 (by decide) v15
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v17 : (vv ε 17 : ℤ) = 617 := vv_even_to ε hε 16 (by decide) v16
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v18 : (vv ε 18 : ℤ) = 873 := vv_odd_to ε 17 (by decide) v17
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  exact ⟨v17, v18⟩
/-- **Stoll Theorem 3.2, pair 4.**  For `ε ∈ [77 / 2 * √2 - 54, 309 / 2 * √2 - 218)`,
`v_{2k+1} − 2 v_{2k−1}` (k=m+9) is the (m+1)-th binary digit of `181√2`. -/
theorem stoll_pair4 {ε : ℝ} (hlo : 77 / 2 * Real.sqrt 2 - 54 ≤ ε) (hhi : ε < 309 / 2 * Real.sqrt 2 - 218) (m : ℕ) :
    (vv ε (2 * (m + 9) + 1) : ℤ) - 2 * (vv ε (2 * (m + 9) - 1) : ℤ)
      = binDigit (181 * Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have hε1 : ε < Real.sqrt 2 / 2 := by nlinarith [hhi, hs2, hsnn]
  obtain ⟨hbp, hbq⟩ := stoll_pair4_base hlo hhi
  have hf1 : ⌊(181 : ℝ) * Real.sqrt 2⌋ = 255 :=
    floor_mul_sqrt2 181 255 (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊(362 : ℝ) * Real.sqrt 2⌋ = 511 :=
    floor_mul_sqrt2 362 511 (by norm_num) (by norm_num) (by norm_num)
  have baseP : (vv ε (2 * (7 + 2) - 1) : ℤ) = ⌊((181 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (181 : ℤ) * 2 ^ 1 := by
    have he : ((181 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = (181 : ℝ) * Real.sqrt 2 := by push_cast; ring
    rw [show (2 * (7 + 2) - 1 : ℕ) = 17 from rfl, he, hf1, hbp]; norm_num
  have baseQ : (vv ε (2 * (7 + 2)) : ℤ) = ⌊((181 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (181 : ℤ) * 2 ^ 1 := by
    have he : ((181 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = (362 : ℝ) * Real.sqrt 2 := by push_cast; ring
    rw [show (2 * (7 + 2) : ℕ) = 18 from rfl, he, hf2, hbq]; norm_num
  have key := stoll_digit 181 7 hε0 hε1 baseP baseQ m
  have i1 : 2 * (7 + 2 + m) + 1 = 2 * (m + 9) + 1 := by ring
  have i2 : 2 * (7 + 2 + m) - 1 = 2 * (m + 9) - 1 := by omega
  rw [i1, i2] at key
  simpa using key

set_option maxHeartbeats 4000000 in
/-- Base case for pair 7 (α=46341, l=15): `vv ε 33 = 158218`, `vv ε 34 = 223754` for
`ε ∈ [79109 / 2 * √2 - 55938, 5 / 2 * √2 - 3)`. -/
private lemma stoll_pair7_base {ε : ℝ} (hlo : 79109 / 2 * Real.sqrt 2 - 55938 ≤ ε) (hhi : ε < 5 / 2 * Real.sqrt 2 - 3) :
    (vv ε 33 : ℤ) = 158218 ∧ (vv ε 34 : ℤ) = 223754 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hε : 0 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have v0 : (vv ε 0 : ℤ) = 1 := by simp [vv]
  have v1 : (vv ε 1 : ℤ) = 2 := vv_even_to ε hε 0 (by decide) v0
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v2 : (vv ε 2 : ℤ) = 3 := vv_odd_to ε 1 (by decide) v1
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v3 : (vv ε 3 : ℤ) = 4 := vv_even_to ε hε 2 (by decide) v2
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v4 : (vv ε 4 : ℤ) = 6 := vv_odd_to ε 3 (by decide) v3
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v5 : (vv ε 5 : ℤ) = 9 := vv_even_to ε hε 4 (by decide) v4
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v6 : (vv ε 6 : ℤ) = 13 := vv_odd_to ε 5 (by decide) v5
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v7 : (vv ε 7 : ℤ) = 19 := vv_even_to ε hε 6 (by decide) v6
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v8 : (vv ε 8 : ℤ) = 27 := vv_odd_to ε 7 (by decide) v7
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v9 : (vv ε 9 : ℤ) = 38 := vv_even_to ε hε 8 (by decide) v8
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v10 : (vv ε 10 : ℤ) = 54 := vv_odd_to ε 9 (by decide) v9
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v11 : (vv ε 11 : ℤ) = 77 := vv_even_to ε hε 10 (by decide) v10
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v12 : (vv ε 12 : ℤ) = 109 := vv_odd_to ε 11 (by decide) v11
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v13 : (vv ε 13 : ℤ) = 154 := vv_even_to ε hε 12 (by decide) v12
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v14 : (vv ε 14 : ℤ) = 218 := vv_odd_to ε 13 (by decide) v13
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v15 : (vv ε 15 : ℤ) = 309 := vv_even_to ε hε 14 (by decide) v14
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v16 : (vv ε 16 : ℤ) = 437 := vv_odd_to ε 15 (by decide) v15
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v17 : (vv ε 17 : ℤ) = 618 := vv_even_to ε hε 16 (by decide) v16
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v18 : (vv ε 18 : ℤ) = 874 := vv_odd_to ε 17 (by decide) v17
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v19 : (vv ε 19 : ℤ) = 1236 := vv_even_to ε hε 18 (by decide) v18
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v20 : (vv ε 20 : ℤ) = 1748 := vv_odd_to ε 19 (by decide) v19
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v21 : (vv ε 21 : ℤ) = 2472 := vv_even_to ε hε 20 (by decide) v20
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v22 : (vv ε 22 : ℤ) = 3496 := vv_odd_to ε 21 (by decide) v21
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v23 : (vv ε 23 : ℤ) = 4944 := vv_even_to ε hε 22 (by decide) v22
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v24 : (vv ε 24 : ℤ) = 6992 := vv_odd_to ε 23 (by decide) v23
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v25 : (vv ε 25 : ℤ) = 9888 := vv_even_to ε hε 24 (by decide) v24
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v26 : (vv ε 26 : ℤ) = 13984 := vv_odd_to ε 25 (by decide) v25
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v27 : (vv ε 27 : ℤ) = 19777 := vv_even_to ε hε 26 (by decide) v26
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v28 : (vv ε 28 : ℤ) = 27969 := vv_odd_to ε 27 (by decide) v27
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v29 : (vv ε 29 : ℤ) = 39554 := vv_even_to ε hε 28 (by decide) v28
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v30 : (vv ε 30 : ℤ) = 55938 := vv_odd_to ε 29 (by decide) v29
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v31 : (vv ε 31 : ℤ) = 79109 := vv_even_to ε hε 30 (by decide) v30
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v32 : (vv ε 32 : ℤ) = 111877 := vv_odd_to ε 31 (by decide) v31
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  have v33 : (vv ε 33 : ℤ) = 158218 := vv_even_to ε hε 32 (by decide) v32
    (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos]) (by push_cast; nlinarith [hlo, hhi, hs1, hs2, hspos])
  have v34 : (vv ε 34 : ℤ) = 223754 := vv_odd_to ε 33 (by decide) v33
    (by push_cast; nlinarith [hs1, hs2, hspos]) (by push_cast; nlinarith [hs1, hs2, hspos])
  exact ⟨v33, v34⟩
/-- **Stoll Theorem 3.2, pair 7.**  For `ε ∈ [79109 / 2 * √2 - 55938, 5 / 2 * √2 - 3)`,
`v_{2k+1} − 2 v_{2k−1}` (k=m+17) is the (m+1)-th binary digit of `46341√2`. -/
theorem stoll_pair7 {ε : ℝ} (hlo : 79109 / 2 * Real.sqrt 2 - 55938 ≤ ε) (hhi : ε < 5 / 2 * Real.sqrt 2 - 3) (m : ℕ) :
    (vv ε (2 * (m + 17) + 1) : ℤ) - 2 * (vv ε (2 * (m + 17) - 1) : ℤ)
      = binDigit (46341 * Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have hε1 : ε < Real.sqrt 2 / 2 := by nlinarith [hhi, hs2, hsnn]
  obtain ⟨hbp, hbq⟩ := stoll_pair7_base hlo hhi
  have hf1 : ⌊(46341 : ℝ) * Real.sqrt 2⌋ = 65536 :=
    floor_mul_sqrt2 46341 65536 (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊(92682 : ℝ) * Real.sqrt 2⌋ = 131072 :=
    floor_mul_sqrt2 92682 131072 (by norm_num) (by norm_num) (by norm_num)
  have baseP : (vv ε (2 * (15 + 2) - 1) : ℤ) = ⌊((46341 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0⌋ + (46341 : ℤ) * 2 ^ 1 := by
    have he : ((46341 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 0 = (46341 : ℝ) * Real.sqrt 2 := by push_cast; ring
    rw [show (2 * (15 + 2) - 1 : ℕ) = 33 from rfl, he, hf1, hbp]; norm_num
  have baseQ : (vv ε (2 * (15 + 2)) : ℤ) = ⌊((46341 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1⌋ + (46341 : ℤ) * 2 ^ 1 := by
    have he : ((46341 : ℤ) : ℝ) * Real.sqrt 2 * 2 ^ 1 = (92682 : ℝ) * Real.sqrt 2 := by push_cast; ring
    rw [show (2 * (15 + 2) : ℕ) = 34 from rfl, he, hf2, hbq]; norm_num
  have key := stoll_digit 46341 15 hε0 hε1 baseP baseQ m
  have i1 : 2 * (15 + 2 + m) + 1 = 2 * (m + 17) + 1 := by ring
  have i2 : 2 * (15 + 2 + m) - 1 = 2 * (m + 17) - 1 := by omega
  rw [i1, i2] at key
  simpa using key


/-! ## Faithful `tᵢ`-form restatements (verbatim Theorem 3.2)

The pair theorems above conclude in terms of `binDigit (αᵢ√2)`.  Stoll's Theorem 3.2 is stated for
`tᵢ = (αᵢ√2 − βᵢ)·2^{−lᵢ}` (Section 4 decomposition).  `binDigit_div_pow` bridges the two: the
`(m+1)`-th digit of `αᵢ√2` is the `(m+1+lᵢ)`-th digit of `tᵢ`.  Composing gives each pair's
conclusion as a digit of `tᵢ` itself — the verbatim paper statement.  The digit index `m+1+lᵢ`
equals `k−1` with `k = lᵢ+2+m`, matching the paper's "`v_{2k+1} − 2v_{2k−1}` = `k`-th digit of `tᵢ`". -/

/-- **Theorem 3.2, pair 1 (verbatim `t₁` form).** `t₁ = √2 − 1`. -/
theorem stoll_pair1_t {ε : ℝ} (hε0 : 1 - Real.sqrt 2 / 2 ≤ ε) (hε1 : ε < Real.sqrt 2 - 1) (m : ℕ) :
    (vv ε (2 * (m + 2) + 1) : ℤ) - 2 * (vv ε (2 * (m + 2) - 1) : ℤ)
      = binDigit (Real.sqrt 2 - 1) (m + 1) := by
  have key := stoll_pair1 hε0 hε1 m
  have conv := binDigit_div_pow 1 1 0 (m + 1) (by norm_num)
  simp only [Int.cast_one, one_mul, pow_zero, div_one, add_zero] at conv
  rw [key]; exact conv.symm

/-- **Theorem 3.2, pair 2 (verbatim `t₂` form).** `t₂ = (11√2 − 5)/2³`. -/
theorem stoll_pair2_t {ε : ℝ} (hlo : Real.sqrt 2 - 1 ≤ ε) (hhi : ε < 19 / 2 * Real.sqrt 2 - 13)
    (m : ℕ) :
    (vv ε (2 * (m + 5) + 1) : ℤ) - 2 * (vv ε (2 * (m + 5) - 1) : ℤ)
      = binDigit (((11 : ℝ) * Real.sqrt 2 - 5) / 2 ^ 3) (m + 1 + 3) := by
  have key := stoll_pair2 hlo hhi m
  have conv := binDigit_div_pow 11 5 3 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

/-- **Theorem 3.2, pair 3 (verbatim `t₃` form).** `t₃ = (45√2 − 19)/2⁵`. -/
theorem stoll_pair3_t {ε : ℝ} (hlo : 19 / 2 * Real.sqrt 2 - 13 ≤ ε) (hhi : ε < 77 / 2 * Real.sqrt 2 - 54)
    (m : ℕ) :
    (vv ε (2 * (m + 7) + 1) : ℤ) - 2 * (vv ε (2 * (m + 7) - 1) : ℤ)
      = binDigit (((45 : ℝ) * Real.sqrt 2 - 19) / 2 ^ 5) (m + 1 + 5) := by
  have key := stoll_pair3 hlo hhi m
  have conv := binDigit_div_pow 45 19 5 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

/-- **Theorem 3.2, pair 4 (verbatim `t₄` form).** `t₄ = (181√2 − 75)/2⁷`. -/
theorem stoll_pair4_t {ε : ℝ} (hlo : 77 / 2 * Real.sqrt 2 - 54 ≤ ε) (hhi : ε < 309 / 2 * Real.sqrt 2 - 218)
    (m : ℕ) :
    (vv ε (2 * (m + 9) + 1) : ℤ) - 2 * (vv ε (2 * (m + 9) - 1) : ℤ)
      = binDigit (((181 : ℝ) * Real.sqrt 2 - 75) / 2 ^ 7) (m + 1 + 7) := by
  have key := stoll_pair4 hlo hhi m
  have conv := binDigit_div_pow 181 75 7 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

/-- **Theorem 3.2, pair 7 (verbatim `t₇` form).** `t₇ = (46341√2 − 19195)/2¹⁵`. -/
theorem stoll_pair7_t {ε : ℝ} (hlo : 79109 / 2 * Real.sqrt 2 - 55938 ≤ ε) (hhi : ε < 5 / 2 * Real.sqrt 2 - 3)
    (m : ℕ) :
    (vv ε (2 * (m + 17) + 1) : ℤ) - 2 * (vv ε (2 * (m + 17) - 1) : ℤ)
      = binDigit (((46341 : ℝ) * Real.sqrt 2 - 19195) / 2 ^ 15) (m + 1 + 15) := by
  have key := stoll_pair7 hlo hhi m
  have conv := binDigit_div_pow 46341 19195 15 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

/-- **Theorem 3.2, pair 8 (verbatim `t₈` form).** `t₈ = (3√2 − 1)/2`. -/
theorem stoll_pair8_t {ε : ℝ} (hlo : 5 / 2 * Real.sqrt 2 - 3 ≤ ε) (hhi : ε < Real.sqrt 2 / 2)
    (m : ℕ) :
    (vv ε (2 * (m + 3) + 1) : ℤ) - 2 * (vv ε (2 * (m + 3) - 1) : ℤ)
      = binDigit (((3 : ℝ) * Real.sqrt 2 - 1) / 2 ^ 1) (m + 1 + 1) := by
  have key := stoll_pair8 hlo hhi m
  have conv := binDigit_div_pow 3 1 1 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

/-- **Corollary 3.3, UNCONDITIONAL, verbatim `t₆` form.**  Stoll's title result stated for
`t₆ = (759250125√2 − 314491699)/2²⁹` itself: for the paper's sequence `w` (`ε = 1 − π²/e³`) and every
`m`, `w_{2k+1} − 2 w_{2k−1}` (with `k = m + 31`) equals the `(m+30)`-th = `(k−1)`-th binary digit of
`t₆`.  This is the digit sequence of `759250125√2/2²⁹` (`= t₆ + 314491699/2²⁹`), Stoll's
"binary digits of 759250125√2". -/
theorem cor33_unconditional_t (m : ℕ) :
    (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) + 1) : ℤ)
        - 2 * (vv (1 - Real.pi ^ 2 / Real.exp 3) (2 * (m + 31) - 1) : ℤ)
      = binDigit (((759250125 : ℝ) * Real.sqrt 2 - 314491699) / 2 ^ 29) (m + 1 + 29) := by
  have key := cor33_unconditional m
  have conv := binDigit_div_pow 759250125 314491699 29 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

set_option maxHeartbeats 1000000 in
/-- **Pair 6 base case, FULL interval (eq 9).**  For every `ε` in the pair-6 interval
`[1296121037√2/2 − 916495974, 79109√2/2 − 55938)`, the 62-step recurrence gives
`vv ε 61 = 2592242074`, `vv ε 62 = 3665983898`.  Unlike `cor33_base_of_bounds` (which covers only
an *interior* `ε` via rational `√2`-enclosures), this covers the **whole half-open interval**: the
two endpoint-defining steps (indices 30, 58) are *exactly* tight, and close because the
`√2`-coefficient of the **exact** product bounds `hpl`/`hph` cancels to `0` there
(`√2·ξ₁ = 1296121037 − 916495974√2`, `√2·ξ₂ = 79109 − 55938√2`, via `√2·√2 = 2`).  All other steps
have margin `≥ 0.0074`, closed by the 13-digit `√2` bounds.  This is Stoll's eq (9) for pair 6 and
makes `stoll_pair6` hold for the full `ε`-interval, completing Theorem 3.2's pair 6. -/
private lemma cor33_base_interval {ε : ℝ}
    (hlo : (1296121037 : ℝ) * Real.sqrt 2 / 2 - 916495974 ≤ ε)
    (hhi : ε < (79109 : ℝ) * Real.sqrt 2 / 2 - 55938) :
    (vv ε 61 : ℤ) = 2592242074 ∧ (vv ε 62 : ℤ) = 3665983898 := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2lo : (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2 := sqrt2_lo
  have hs2hi : Real.sqrt 2 < (14142135623731 / 10000000000000 : ℝ) := sqrt2_hi
  have hεpos : (0:ℝ) ≤ ε := by nlinarith [hlo, hs2lo]
  have hpl : Real.sqrt 2 * ε ≥ 1296121037 - 916495974 * Real.sqrt 2 := by
    have h := mul_le_mul_of_nonneg_left hlo hsnn
    nlinarith [h, hs2]
  have hph : Real.sqrt 2 * ε < 79109 - 55938 * Real.sqrt 2 := by
    have h := mul_lt_mul_of_pos_left hhi hspos
    nlinarith [h, hs2]
  have v0 : (vv ε 0 : ℤ) = 1 := by simp [vv]
  have v1 : (vv ε 1 : ℤ) = 2 := vv_even_to ε hεpos 0 (by decide) v0
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v2 : (vv ε 2 : ℤ) = 3 := vv_odd_to ε 1 (by decide) v1
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v3 : (vv ε 3 : ℤ) = 4 := vv_even_to ε hεpos 2 (by decide) v2
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v4 : (vv ε 4 : ℤ) = 6 := vv_odd_to ε 3 (by decide) v3
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v5 : (vv ε 5 : ℤ) = 9 := vv_even_to ε hεpos 4 (by decide) v4
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v6 : (vv ε 6 : ℤ) = 13 := vv_odd_to ε 5 (by decide) v5
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v7 : (vv ε 7 : ℤ) = 19 := vv_even_to ε hεpos 6 (by decide) v6
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v8 : (vv ε 8 : ℤ) = 27 := vv_odd_to ε 7 (by decide) v7
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v9 : (vv ε 9 : ℤ) = 38 := vv_even_to ε hεpos 8 (by decide) v8
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v10 : (vv ε 10 : ℤ) = 54 := vv_odd_to ε 9 (by decide) v9
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v11 : (vv ε 11 : ℤ) = 77 := vv_even_to ε hεpos 10 (by decide) v10
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v12 : (vv ε 12 : ℤ) = 109 := vv_odd_to ε 11 (by decide) v11
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v13 : (vv ε 13 : ℤ) = 154 := vv_even_to ε hεpos 12 (by decide) v12
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v14 : (vv ε 14 : ℤ) = 218 := vv_odd_to ε 13 (by decide) v13
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v15 : (vv ε 15 : ℤ) = 309 := vv_even_to ε hεpos 14 (by decide) v14
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v16 : (vv ε 16 : ℤ) = 437 := vv_odd_to ε 15 (by decide) v15
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v17 : (vv ε 17 : ℤ) = 618 := vv_even_to ε hεpos 16 (by decide) v16
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v18 : (vv ε 18 : ℤ) = 874 := vv_odd_to ε 17 (by decide) v17
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v19 : (vv ε 19 : ℤ) = 1236 := vv_even_to ε hεpos 18 (by decide) v18
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v20 : (vv ε 20 : ℤ) = 1748 := vv_odd_to ε 19 (by decide) v19
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v21 : (vv ε 21 : ℤ) = 2472 := vv_even_to ε hεpos 20 (by decide) v20
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v22 : (vv ε 22 : ℤ) = 3496 := vv_odd_to ε 21 (by decide) v21
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v23 : (vv ε 23 : ℤ) = 4944 := vv_even_to ε hεpos 22 (by decide) v22
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v24 : (vv ε 24 : ℤ) = 6992 := vv_odd_to ε 23 (by decide) v23
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v25 : (vv ε 25 : ℤ) = 9888 := vv_even_to ε hεpos 24 (by decide) v24
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v26 : (vv ε 26 : ℤ) = 13984 := vv_odd_to ε 25 (by decide) v25
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v27 : (vv ε 27 : ℤ) = 19777 := vv_even_to ε hεpos 26 (by decide) v26
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v28 : (vv ε 28 : ℤ) = 27969 := vv_odd_to ε 27 (by decide) v27
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v29 : (vv ε 29 : ℤ) = 39554 := vv_even_to ε hεpos 28 (by decide) v28
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v30 : (vv ε 30 : ℤ) = 55938 := vv_odd_to ε 29 (by decide) v29
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v31 : (vv ε 31 : ℤ) = 79108 := vv_even_to ε hεpos 30 (by decide) v30
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v32 : (vv ε 32 : ℤ) = 111876 := vv_odd_to ε 31 (by decide) v31
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v33 : (vv ε 33 : ℤ) = 158217 := vv_even_to ε hεpos 32 (by decide) v32
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v34 : (vv ε 34 : ℤ) = 223753 := vv_odd_to ε 33 (by decide) v33
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v35 : (vv ε 35 : ℤ) = 316435 := vv_even_to ε hεpos 34 (by decide) v34
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v36 : (vv ε 36 : ℤ) = 447507 := vv_odd_to ε 35 (by decide) v35
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v37 : (vv ε 37 : ℤ) = 632871 := vv_even_to ε hεpos 36 (by decide) v36
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v38 : (vv ε 38 : ℤ) = 895015 := vv_odd_to ε 37 (by decide) v37
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v39 : (vv ε 39 : ℤ) = 1265743 := vv_even_to ε hεpos 38 (by decide) v38
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v40 : (vv ε 40 : ℤ) = 1790031 := vv_odd_to ε 39 (by decide) v39
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v41 : (vv ε 41 : ℤ) = 2531486 := vv_even_to ε hεpos 40 (by decide) v40
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v42 : (vv ε 42 : ℤ) = 3580062 := vv_odd_to ε 41 (by decide) v41
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v43 : (vv ε 43 : ℤ) = 5062972 := vv_even_to ε hεpos 42 (by decide) v42
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v44 : (vv ε 44 : ℤ) = 7160124 := vv_odd_to ε 43 (by decide) v43
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v45 : (vv ε 45 : ℤ) = 10125945 := vv_even_to ε hεpos 44 (by decide) v44
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v46 : (vv ε 46 : ℤ) = 14320249 := vv_odd_to ε 45 (by decide) v45
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v47 : (vv ε 47 : ℤ) = 20251891 := vv_even_to ε hεpos 46 (by decide) v46
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v48 : (vv ε 48 : ℤ) = 28640499 := vv_odd_to ε 47 (by decide) v47
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v49 : (vv ε 49 : ℤ) = 40503782 := vv_even_to ε hεpos 48 (by decide) v48
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v50 : (vv ε 50 : ℤ) = 57280998 := vv_odd_to ε 49 (by decide) v49
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v51 : (vv ε 51 : ℤ) = 81007564 := vv_even_to ε hεpos 50 (by decide) v50
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v52 : (vv ε 52 : ℤ) = 114561996 := vv_odd_to ε 51 (by decide) v51
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v53 : (vv ε 53 : ℤ) = 162015129 := vv_even_to ε hεpos 52 (by decide) v52
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v54 : (vv ε 54 : ℤ) = 229123993 := vv_odd_to ε 53 (by decide) v53
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v55 : (vv ε 55 : ℤ) = 324030259 := vv_even_to ε hεpos 54 (by decide) v54
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v56 : (vv ε 56 : ℤ) = 458247987 := vv_odd_to ε 55 (by decide) v55
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v57 : (vv ε 57 : ℤ) = 648060518 := vv_even_to ε hεpos 56 (by decide) v56
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v58 : (vv ε 58 : ℤ) = 916495974 := vv_odd_to ε 57 (by decide) v57
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v59 : (vv ε 59 : ℤ) = 1296121037 := vv_even_to ε hεpos 58 (by decide) v58
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v60 : (vv ε 60 : ℤ) = 1832991949 := vv_odd_to ε 59 (by decide) v59
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  have v61 : (vv ε 61 : ℤ) = 2592242074 := vv_even_to ε hεpos 60 (by decide) v60
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi, hpl, hph])
  have v62 : (vv ε 62 : ℤ) = 3665983898 := vv_odd_to ε 61 (by decide) v61
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
    (by push_cast; rw [mul_add]; linarith [hs2lo, hs2hi])
  exact ⟨v61, v62⟩

/-- **Stoll Theorem 3.2, pair 6 (full interval).**  For *every* offset
`ε ∈ [1296121037√2/2 − 916495974, 79109√2/2 − 55938)` (pair 6's interval `[ξ₁₆, ξ₂₆)`) and every
`m`, `v_{2k+1} − 2 v_{2k−1}` (`k = m + 31`) equals the `(m+1)`-th binary digit of `759250125√2`.
This is the pair-6 row of Theorem 3.2 for its *whole* `ε`-interval — `cor33_unconditional` is the
special case `ε = 1 − π²/e³` (interior to this interval). -/
theorem stoll_pair6 {ε : ℝ}
    (hlo : (1296121037 : ℝ) * Real.sqrt 2 / 2 - 916495974 ≤ ε)
    (hhi : ε < (79109 : ℝ) * Real.sqrt 2 / 2 - 55938) (m : ℕ) :
    (vv ε (2 * (m + 31) + 1) : ℤ) - 2 * (vv ε (2 * (m + 31) - 1) : ℤ)
      = binDigit (759250125 * Real.sqrt 2) (m + 1) := by
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε0 : 1 - Real.sqrt 2 / 2 ≤ ε := by nlinarith [hlo, hs2, hsnn]
  have hε1 : ε < Real.sqrt 2 / 2 := by nlinarith [hhi, hs2, hsnn]
  obtain ⟨b61, b62⟩ := cor33_base_interval hlo hhi
  exact cor33 hε0 hε1 b61 b62 m

/-- **Stoll Theorem 3.2, pair 6 (full interval, verbatim `t₆` form).**
`t₆ = (759250125√2 − 314491699)/2²⁹`.  For every `ε ∈ [ξ₁₆, ξ₂₆)`, `v_{2k+1} − 2 v_{2k−1}`
(`k = m + 31`) is the `(m+30)`-th = `(k−1)`-th binary digit of `t₆`. -/
theorem stoll_pair6_t {ε : ℝ}
    (hlo : (1296121037 : ℝ) * Real.sqrt 2 / 2 - 916495974 ≤ ε)
    (hhi : ε < (79109 : ℝ) * Real.sqrt 2 / 2 - 55938) (m : ℕ) :
    (vv ε (2 * (m + 31) + 1) : ℤ) - 2 * (vv ε (2 * (m + 31) - 1) : ℤ)
      = binDigit (((759250125 : ℝ) * Real.sqrt 2 - 314491699) / 2 ^ 29) (m + 1 + 29) := by
  have key := stoll_pair6 hlo hhi m
  have conv := binDigit_div_pow 759250125 314491699 29 (m + 1) (by norm_num)
  push_cast at conv
  rw [key]; exact conv.symm

/-! ## Completeness: the 8 intervals are disjoint and exactly cover `[1−√2/2, √2/2)`

Stoll's Theorem 3.2 partitions the admissible offset range.  The eight `[ξ₁ᵢ, ξ₂ᵢ)` are consecutive
(`ξ₂ᵢ = ξ₁,ᵢ₊₁`), so it suffices that the nine endpoints are strictly increasing; then every
`ε ∈ [1−√2/2, √2/2)` lies in exactly one pair interval, and `stoll_pair{1..8}` extracts the digits
of the corresponding `tᵢ`.  This realizes the full Theorem 3.2 over the whole admissible range. -/

/-- The nine interval endpoints `1−√2/2 < √2−1 < 19√2/2−13 < 77√2/2−54 < 309√2/2−218 <
1296121037√2/2−916495974 < 79109√2/2−55938 < 5√2/2−3 < √2/2` are strictly increasing, so the eight
pair intervals are nonempty and pairwise disjoint. -/
theorem stoll_endpoints_strictMono :
    1 - Real.sqrt 2 / 2 < Real.sqrt 2 - 1 ∧
    Real.sqrt 2 - 1 < 19 / 2 * Real.sqrt 2 - 13 ∧
    (19 : ℝ) / 2 * Real.sqrt 2 - 13 < 77 / 2 * Real.sqrt 2 - 54 ∧
    (77 : ℝ) / 2 * Real.sqrt 2 - 54 < 309 / 2 * Real.sqrt 2 - 218 ∧
    (309 : ℝ) / 2 * Real.sqrt 2 - 218 < 1296121037 / 2 * Real.sqrt 2 - 916495974 ∧
    (1296121037 : ℝ) / 2 * Real.sqrt 2 - 916495974 < 79109 / 2 * Real.sqrt 2 - 55938 ∧
    (79109 : ℝ) / 2 * Real.sqrt 2 - 55938 < 5 / 2 * Real.sqrt 2 - 3 ∧
    (5 : ℝ) / 2 * Real.sqrt 2 - 3 < Real.sqrt 2 / 2 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlo : (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2 := sqrt2_lo
  have hhi : Real.sqrt 2 < (14142135623731 / 10000000000000 : ℝ) := sqrt2_hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hs2, hlo, hhi]

/-- **Completeness of Theorem 3.2.**  Every admissible offset `ε ∈ [1−√2/2, √2/2)` lies in exactly
one of the eight pair intervals `[ξ₁ᵢ, ξ₂ᵢ)`.  Combined with `stoll_pair{1..8}`, this shows the
parametrized recurrence reproduces the binary digits of the corresponding `tᵢ` for the *whole*
admissible range of `ε` — the full content of Stoll's Theorem 3.2. -/
theorem stoll_intervals_cover {ε : ℝ} (h0 : 1 - Real.sqrt 2 / 2 ≤ ε) (h8 : ε < Real.sqrt 2 / 2) :
    (1 - Real.sqrt 2 / 2 ≤ ε ∧ ε < Real.sqrt 2 - 1) ∨
    (Real.sqrt 2 - 1 ≤ ε ∧ ε < 19 / 2 * Real.sqrt 2 - 13) ∨
    ((19 : ℝ) / 2 * Real.sqrt 2 - 13 ≤ ε ∧ ε < 77 / 2 * Real.sqrt 2 - 54) ∨
    ((77 : ℝ) / 2 * Real.sqrt 2 - 54 ≤ ε ∧ ε < 309 / 2 * Real.sqrt 2 - 218) ∨
    ((309 : ℝ) / 2 * Real.sqrt 2 - 218 ≤ ε ∧ ε < 1296121037 / 2 * Real.sqrt 2 - 916495974) ∨
    ((1296121037 : ℝ) / 2 * Real.sqrt 2 - 916495974 ≤ ε ∧ ε < 79109 / 2 * Real.sqrt 2 - 55938) ∨
    ((79109 : ℝ) / 2 * Real.sqrt 2 - 55938 ≤ ε ∧ ε < 5 / 2 * Real.sqrt 2 - 3) ∨
    ((5 : ℝ) / 2 * Real.sqrt 2 - 3 ≤ ε ∧ ε < Real.sqrt 2 / 2) := by
  rcases lt_or_ge ε (Real.sqrt 2 - 1) with h | h1
  · exact Or.inl ⟨h0, h⟩
  rcases lt_or_ge ε (19 / 2 * Real.sqrt 2 - 13) with h | h2
  · exact Or.inr (Or.inl ⟨h1, h⟩)
  rcases lt_or_ge ε (77 / 2 * Real.sqrt 2 - 54) with h | h3
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h⟩))
  rcases lt_or_ge ε (309 / 2 * Real.sqrt 2 - 218) with h | h4
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h⟩)))
  rcases lt_or_ge ε (1296121037 / 2 * Real.sqrt 2 - 916495974) with h | h5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, h⟩))))
  rcases lt_or_ge ε (79109 / 2 * Real.sqrt 2 - 55938) with h | h6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, h⟩)))))
  rcases lt_or_ge ε (5 / 2 * Real.sqrt 2 - 3) with h | h7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h7, h8⟩))))))

/-- **Structural: `vv` is `≥ 1` and (weakly) monotone** for any nonnegative offset `ε`.  Mirrors the
headline's `u_pos`/`u_strictMono`; reusable infrastructure for any uniform statement over the
sequence. (Strict monotonicity fails near the start for small `ε`, so only `≤` holds universally.) -/
theorem vv_one_le_and_mono (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    1 ≤ vv ε n ∧ vv ε n ≤ vv ε (n + 1) := by
  have h_lower_bound : ∀ n, 1 ≤ vv ε n := by
    intro n; induction' n with n ih <;> norm_num [ *, vv ]
    exact one_le_mul_of_one_le_of_one_le ( Real.le_sqrt_of_sq_le ( by norm_num ) ) ( le_add_of_le_of_nonneg ( mod_cast ih ) ( by positivity ) )
  refine' ⟨ h_lower_bound _, Nat.le_floor _ ⟩
  split_ifs <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( vv ε n : ℝ ) ≥ 1 by exact_mod_cast h_lower_bound n ]

/-- **Master theorem (7 of 8 pairs): the Graham–Pollak difference is a binary digit.**  For every
offset `ε` in any of the seven explicitly-formalized pair intervals (i.e. `ε ∈ [1−√2/2, √2/2)`
*except* pair 5's interval `[309/2√2−218, 1296121037/2√2−916495974)`), and every `k ≥ 31`, the
difference `vv ε (2k+1) − 2 vv ε (2k−1)` is `0` or `1` — a genuine bit of the corresponding `tᵢ`.
`k ≥ 31` is the uniform threshold (max `lᵢ+2 = 31`, pair 6).  Pair 5's interval is the one remaining
case (the special `t=√2` / Diophantine thread — see `PENDING_WORK.md`). -/
theorem stoll_gp_isBit {ε : ℝ} {k : ℕ} (hk : 31 ≤ k)
    (hmem :
      (1 - Real.sqrt 2 / 2 ≤ ε ∧ ε < Real.sqrt 2 - 1) ∨
      (Real.sqrt 2 - 1 ≤ ε ∧ ε < 19 / 2 * Real.sqrt 2 - 13) ∨
      ((19 : ℝ) / 2 * Real.sqrt 2 - 13 ≤ ε ∧ ε < 77 / 2 * Real.sqrt 2 - 54) ∨
      ((77 : ℝ) / 2 * Real.sqrt 2 - 54 ≤ ε ∧ ε < 309 / 2 * Real.sqrt 2 - 218) ∨
      ((1296121037 : ℝ) / 2 * Real.sqrt 2 - 916495974 ≤ ε ∧ ε < 79109 / 2 * Real.sqrt 2 - 55938) ∨
      ((79109 : ℝ) / 2 * Real.sqrt 2 - 55938 ≤ ε ∧ ε < 5 / 2 * Real.sqrt 2 - 3) ∨
      ((5 : ℝ) / 2 * Real.sqrt 2 - 3 ≤ ε ∧ ε < Real.sqrt 2 / 2)) :
    (vv ε (2 * k + 1) : ℤ) - 2 * (vv ε (2 * k - 1) : ℤ) = 0 ∨
    (vv ε (2 * k + 1) : ℤ) - 2 * (vv ε (2 * k - 1) : ℤ) = 1 := by
  rcases hmem with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
  · have h := stoll_pair1 a b (k - 2)
    rw [show k - 2 + 2 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)
  · have h := stoll_pair2 a b (k - 5)
    rw [show k - 5 + 5 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)
  · have h := stoll_pair3 a b (k - 7)
    rw [show k - 7 + 7 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)
  · have h := stoll_pair4 a b (k - 9)
    rw [show k - 9 + 9 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)
  · have a' : (1296121037 : ℝ) * Real.sqrt 2 / 2 - 916495974 ≤ ε := by
      rw [show (1296121037 : ℝ) * Real.sqrt 2 / 2 = 1296121037 / 2 * Real.sqrt 2 from by ring]; exact a
    have b' : ε < (79109 : ℝ) * Real.sqrt 2 / 2 - 55938 := by
      rw [show (79109 : ℝ) * Real.sqrt 2 / 2 = 79109 / 2 * Real.sqrt 2 from by ring]; exact b
    have h := stoll_pair6 a' b' (k - 31)
    rw [show k - 31 + 31 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)
  · have h := stoll_pair7 a b (k - 17)
    rw [show k - 17 + 17 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)
  · have h := stoll_pair8 a b (k - 3)
    rw [show k - 3 + 3 = k from by omega] at h
    rw [h]; exact binDigit_mem_zero_one _ _ (by omega)

/-- **The bonus sequence at `ε = ½` is the headline sequence.**  `vv (1/2) = u`: both the ε-steps
(even indices) and the ½-steps (odd indices) use offset `½`, so the recurrence collapses to `u`'s.
Hence pair 5's `ε = ½` instance *is* exactly Graham–Pollak (`graham_pollak`), with no extra work; the
open part of pair 5 is only the OTHER `ε` in its interval (the Diophantine thread, see PENDING_WORK). -/
theorem vv_half_eq_u (n : ℕ) : vv (1 / 2) n = u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ⌊Real.sqrt 2 * ((vv (1/2) n : ℝ) + (if Even n then (1/2 : ℝ) else 1/2))⌋₊ = u (n + 1)
    rw [ih, ite_self]; rfl

/-- Pair 5 at `ε = ½` (Graham–Pollak, restated through `vv`): `vv (1/2) (2n+1) − 2 vv (1/2) (2n−1)`
is the `n`-th binary digit of `√2`. Immediate from `vv_half_eq_u` + `graham_pollak`. -/
theorem stoll_pair5_half (n : ℕ) (hn : 1 ≤ n) :
    (vv (1 / 2) (2 * n + 1) : ℤ) - 2 * (vv (1 / 2) (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  rw [vv_half_eq_u, vv_half_eq_u]; exact graham_pollak n hn

/-- **Pair 5 reduction (isolates the Diophantine core).**  If the even-index (ε-)steps of `vv ε`
land on the headline sequence `u` — i.e. `⌊√2·(u(2j)+ε)⌋₊ = u(2j+1)` for every `j` — then
`vv ε = u` entirely (the odd ½-steps match `u` automatically, being literally `u`'s recurrence).
This reduces pair 5's full-interval statement to the single hypothesis `Heven`, which is the
genuinely hard part: for `ε ∈ [ξ₁,ξ₂)` (pair 5's interval) `Heven` holds, but proving it needs a
Diophantine bound on `‖√2·2^j‖` (√2 badly approximable; the per-step margin shrinks — see
`PENDING_WORK.md §1`).  Axiom-free.  Combined with the headline `graham_pollak`, `Heven` ⟹ pair 5. -/
theorem vv_eq_u_of_evenstep {ε : ℝ}
    (Heven : ∀ j, ⌊Real.sqrt 2 * ((u (2 * j) : ℝ) + ε)⌋₊ = u (2 * j + 1)) :
    ∀ n, vv ε n = u n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show ⌊Real.sqrt 2 * ((vv ε n : ℝ) + (if Even n then ε else 1 / 2))⌋₊ = u (n + 1)
    rw [ih]
    by_cases hn : Even n
    · rw [if_pos hn]
      obtain ⟨j, rfl⟩ := hn
      rw [show j + j = 2 * j from by ring]
      exact Heven j
    · rw [if_neg hn]; rfl

/-- **Pair 5 modulo the Diophantine core.**  Given the even-step agreement `Heven` (which holds for
every `ε` in pair 5's interval `[ξ₁,ξ₂)` — the open Diophantine lemma), `vv ε` reproduces the binary
digits of `√2`: `vv ε (2k+1) − 2 vv ε (2k−1) = binDigit √2 k` for `k ≥ 1`.  Immediate from
`vv_eq_u_of_evenstep` + `graham_pollak`.  Discharging `Heven` for the interval completes pair 5 (the
last open case of Theorem 3.2). -/
theorem stoll_pair5_of_evenstep {ε : ℝ}
    (Heven : ∀ j, ⌊Real.sqrt 2 * ((u (2 * j) : ℝ) + ε)⌋₊ = u (2 * j + 1)) (k : ℕ) (hk : 1 ≤ k) :
    (vv ε (2 * k + 1) : ℤ) - 2 * (vv ε (2 * k - 1) : ℤ) = binDigit (Real.sqrt 2) k := by
  rw [vv_eq_u_of_evenstep Heven, vv_eq_u_of_evenstep Heven]
  exact graham_pollak k hk

/-- **√2 is badly approximable** (irrationality measure 2, explicit constant): for every integer `p`
and positive natural `q`, `1/(3q) ≤ |q√2 − p|`.  Equivalently `‖q√2‖ ≥ 1/(3q)` — the Diophantine
input the pair-5 even-step (`Heven` in `vv_eq_u_of_evenstep`) needs, since √2's quadratic-irrational
type keeps the floor-recurrence margin positive for all `j`.  (Aristotle-proved, kernel-verified.) -/
theorem sqrt2_badly_approximable (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) / (3 * q) ≤ |(q : ℝ) * Real.sqrt 2 - p| := by
  by_contra! h_contra;
  -- From the assumption |q√2 - p| < 1/(3q), we get |2q² - p²| < (q√2 + p)/(3q).
  have h_abs : |(2 * (q : ℝ) ^ 2 - p ^ 2)| < (q * Real.sqrt 2 + p) / (3 * q) := by
    -- Since $q \geq 1$, we have $q\sqrt{2} \geq \sqrt{2} > 1$, and $1/(3q) \leq 1/3$, so $q\sqrt{2} - p > q\sqrt{2} - 1/(3q) - (q\sqrt{2} - p)$ wait, simpler: since $|q\sqrt{2} - p| < 1/3$ and $q\sqrt{2} \geq \sqrt{2} > 1$, we get $p > q\sqrt{2} - 1/3 > 2/3$, so $p \geq 1$.
    have h_p_ge_1 : (p : ℝ) ≥ 1 := by
      rw [ lt_div_iff₀ ] at h_contra <;> norm_num <;> try linarith;
      exact_mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ abs_lt.mp ( show |↑q * Real.sqrt 2 - ↑p| < 1 / 3 by nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast ] ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( q : ℝ ) ≥ 1 by norm_cast ] );
    rw [ abs_lt ] at *;
    ring_nf at *; constructor <;> nlinarith [ show 0 < ( q : ℝ ) * Real.sqrt 2 by positivity, Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] ;
  -- Since $2q^2 - p^2$ is a nonzero integer, we have $|2q^2 - p^2| \geq 1$.
  have h_nonzero : |(2 * (q : ℝ) ^ 2 - p ^ 2)| ≥ 1 := by
    by_cases h_eq : (2 * (q : ℝ) ^ 2 - p ^ 2) = 0;
    · -- If $2q^2 = p^2$, then $\sqrt{2} = \frac{p}{q}$, which contradicts the irrationality of $\sqrt{2}$.
      have h_contra : Real.sqrt 2 = p / q ∨ Real.sqrt 2 = -p / q := by
        grind;
      exact False.elim <| irrational_sqrt_two <| h_contra.elim ( fun h => ⟨ p / q, by push_cast; linarith ⟩ ) fun h => ⟨ -p / q, by push_cast; ring_nf at *; linarith ⟩;
    · exact mod_cast abs_pos.mpr h_eq;
  -- From the assumption |q√2 - p| < 1/(3q), we get p > q(3 - √2).
  have h_p_gt : (p : ℝ) > q * (3 - Real.sqrt 2) := by
    rw [ lt_div_iff₀ ] at h_abs <;> first | positivity | nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ q ) ] ;
  -- From the assumption |q√2 - p| < 1/(3q), we get p < q√2 + 1/(3q).
  have h_p_lt : (p : ℝ) < q * Real.sqrt 2 + 1 / (3 * q) := by
    linarith [ abs_lt.mp h_contra ];
  rcases q with ( _ | _ | q ) <;> norm_num at *;
  · rcases p with ⟨ _ | _ | _ | p ⟩ <;> norm_num at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  · nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_mul_cancel₀ ( by linarith : ( q : ℝ ) + 1 + 1 ≠ 0 ), mul_le_mul_of_nonneg_left ( show ( q : ℝ ) ≥ 0 by positivity ) ( Real.sqrt_nonneg 2 ) ]

end Erdos482

