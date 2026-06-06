import Mathlib

namespace Erdos482
open Real

/-- The crux universal inequality (Stoll eq (7), generalized): for every real `x`,
`0 ≤ {x} − √2·{x/2} + √2/2 < 1`.  Proof: case-split on parity of `⌊x⌋` (so `{x} = 2{x/2}` or
`2{x/2} − 1`), then `nlinarith [Real.sq_sqrt, Int.fract_nonneg, Int.fract_lt_one]` with `√2² = 2`,
`1 < √2 < 3/2`.  No mathlib lemma supplies this. -/
theorem crux (x : ℝ) :
    0 ≤ Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 ∧
        Int.fract x - Real.sqrt 2 * Int.fract (x / 2) + Real.sqrt 2 / 2 < 1 := by
  sorry

end Erdos482
