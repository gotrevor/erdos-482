import Erdos482.Basic
import Erdos482.Crux

namespace Erdos482
open Real
-- (5)  u (2k)   = ⌊√2·2^{k-2}⌋ + 3·2^{k-3}      (for GP: α=β=1, l=1, γ=3)
-- (6)  u (2k+1) = ⌊√2·2^{k-1}⌋ + 2^k
-- Each induction step (Nat.le_induction from k=3) reduces via Int.floor_eq_iff to `crux`.
end Erdos482
