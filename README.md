# erdos-482 — Graham–Pollak binary-digits identity (Erdős #482), formalized in Lean 4 / mathlib

`u 0 = 1`, `u(n+1) = ⌊√2(u n + ½)⌋` ⟹ `u(2n+1) − 2u(2n−1)` is the n-th binary digit of √2.
Crux = one fractional-part inequality. See `HANDOFF.md` for the attack plan.
