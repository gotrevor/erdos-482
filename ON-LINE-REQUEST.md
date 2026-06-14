# ON-LINE-REQUEST — open-web questions blocking local Lean progress

## 2026-06-14 — Is `{ξ·θ^n}` equidistribution for fixed algebraic `θ`, fixed `ξ` open? (cubic Tier-2)

**Context.** Refuting the previous findings doc's "Tier-1" cubic impossibility this lap, I localized the
genuine cubic obstruction to a single equidistribution input (see `notes/CUBIC-EXPLORATION.md`,
`PENDING_WORK.md` ★ ACTIVE FRONTIER, `src/Erdos482/General/CubicDefect.lean`). The previous findings doc
(`archive/findings/…cubic-selfref-literature.md`, §2) asserted that `{α^n ξ}` for `α=2^{1/3}`
"equidistributes (Weyl — guaranteed precisely because β is non-Pisot)". **I believe this is an
over-claim** and want it checked, because it changes whether an unconditional cubic impossibility is even
provable in current mathematics.

**What I need confirmed/refuted (with citations):**
1. For a **fixed** real base `θ>1` (e.g. `θ=2^{1/3}`, or even rational `3/2`) and a **fixed** real `ξ≠0`,
   is equidistribution of `{ξ·θⁿ} mod 1` a THEOREM or an OPEN problem in general? My understanding: it is
   **open** for specific `ξ` (the `{(3/2)ⁿ}` problem is famously open; Pisot/Salem give the *exceptional*
   `ξ` where it fails to equidistribute, but generic specific `ξ` is not resolved), while it holds for
   **almost every** `ξ` by Weyl/Koksma. Confirm the almost-all result (exact statement + reference —
   Koksma 1935?) and confirm the fixed-`ξ` case is open.
2. Is the doc's specific claim — "non-Pisot ⟹ `{α^n ξ}` equidistributes for our `ξ`" — actually valid, or
   is it conflating the a.e.-`ξ` theorem with the fixed-`ξ` question? (I suspect the latter.)
3. Does mathlib (current) contain the measure-theoretic Weyl/Koksma equidistribution of `{ξ·θⁿ}` for a.e.
   `ξ`? (I only see `n·θ` linear equidistribution via `AddCircle` ergodicity, not the geometric `θⁿ`
   version.) If it exists, give the declaration name; this would unblock PENDING_WORK attack-path #2.

**Why it unblocks me.** If (1)/(2) confirm the fixed-`ξ` case is open, then the unconditional cubic
impossibility is beyond current math and I should formalize only the **conditional** version (attack
path #1) + the **almost-all-`W`** version (attack path #2) — and STATUS/notes should record the cubic as
"open in mathematics, conditional result formalized," not "needs deep machinery we haven't built."
