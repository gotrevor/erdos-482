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

end Erdos482
