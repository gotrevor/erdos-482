import Erdos482.Basic
import Erdos482.Induction
import Erdos482.Digits

namespace Erdos482
open Real

/-- **HEADLINE (Graham–Pollak, Erdős #482).**  For the sequence `u 0 = 1`,
`u (n+1) = ⌊√2·(u n + 1/2)⌋`, the quantity `u(2n+1) − 2·u(2n−1)` equals the `n`-th binary digit of
`√2` (in Stoll's floor-formula sense `binDigit`).  Verified numerically: the digits read
`0,1,1,0,1,…` matching `√2 = 1.0110101…₂`. -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := (gp_pair (m + 1)).1
  have h2 := (gp_pair m).1
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [e2, h1, h2]
  unfold binDigit
  rw [Nat.add_sub_cancel]
  ring

end Erdos482
