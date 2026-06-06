# erdos-482 — Graham–Pollak binary-digits identity (Erdős #482), formalized in Lean 4 / mathlib

A Lean 4 / mathlib formalization of [Erdős problem #482](https://www.erdosproblems.com/482).
The problem is marked **SOLVED** on erdosproblems.com, which lists **no formalized statement** — so
this is (as far as that database knows) the first Lean formalization of #482.

## The problem

> Define `a₁ = 1` and `a(n+1) = ⌊√2·(aₙ + ½)⌋`. Then `a(2n+1) − 2·a(2n−1)` is the n-th digit in the
> binary expansion of √2. Find similar results for `θ = √m` and other algebraic numbers.

Source: `[ErGr80, p.96]`. The √2 result is due to **Graham and Pollak [GrPo70]**; the wide-ranging
generalizations are due to **Stoll [St05, St06]** ([arXiv:0902.4168](https://arxiv.org/abs/0902.4168)).
The only genuinely new content is **one fractional-part inequality** (`0 ≤ {x} − √2{x/2} + √2/2 < 1`,
Stoll eq (7)); mathlib supplies `Int.fract`, `irrational_sqrt_two`, `Real.digits`, and the rest.

## What is proven

`lake build` is green, with **zero `sorry` and zero custom axioms** (every theorem bottoms out at
`[propext, Classical.choice, Quot.sound]`).

- **Headline** — the Graham–Pollak √2 identity (`graham_pollak`), plus its restatement against
  mathlib's `Real.digits` and a concrete first-six-digits certificate.
- **Stoll's Theorem 3.2** — binary-digit identities for the GP-style `(α, l)` pairs (general core +
  the individual pairs). ⚠️ **Pair 5 (`t₅ = √2` itself) is proven only at `ε = ½`** — see
  [`STOLL-PAIR5-ERRATUM.md`](STOLL-PAIR5-ERRATUM.md): the paper's full-interval claim for pair 5 is
  *incorrect* (the digit identity fails at `n = 280` at the stated lower endpoint; validity collapses
  to `ε = ½`), and its printed closed form has a typo. So pair 5's interval is deliberately **not**
  claimed here.
- **Stoll's Corollary 3.3** — the unconditional title result, digits of `759250125·√2`
  (`cor33_unconditional`).

See [`STATUS.md`](STATUS.md) for the full theorem inventory + axiom ledger,
[`PENDING_WORK.md`](PENDING_WORK.md) for the remaining optional polish (notably pair 6 over its full
ε-interval, and the cosmetic `t_i` restatement), and
[`STOLL-PAIR5-ERRATUM.md`](STOLL-PAIR5-ERRATUM.md) for two errors in the source paper's pair-5
treatment (a typo + the over-wide interval claim) and why pair 5 is scoped to `ε = ½`.
