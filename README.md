# erdos-482 — Graham–Pollak binary-digits identity (Erdős #482), formalized in Lean 4 / mathlib

A Lean 4 / mathlib formalization of [Erdős problem #482](https://www.erdosproblems.com/482).
The problem is marked **SOLVED** on erdosproblems.com, which lists **no formalized statement** — so
this is (as far as that database knows) the first Lean formalization of #482.

## The problem

> Define `a₁ = 1` and `a(n+1) = ⌊√2·(aₙ + ½)⌋`. Then `a(2n+1) − 2·a(2n−1)` is the n-th digit in the
> binary expansion of √2. Find similar results for `θ = √m` and other algebraic numbers.

Source: `[ErGr80, p.96]`. The √2 result is due to **Graham and Pollak** (*Math. Mag.* **43** (1970),
143–145). The generalizations formalized here come from two **Thomas Stoll** papers, which should be
kept distinct (see [`papers/SOURCES.md`](papers/SOURCES.md)):

- the **(α, l)-pair family** (Theorem 3.2, Corollary 3.3) — *A fancy way to obtain the binary digits of
  759250125√2*, **Amer. Math. Monthly 117** (2010), no. 7, 611–617
  ([arXiv:0902.4168](https://arxiv.org/abs/0902.4168));
- the **general base-`g` resolution** (any real `w > 0`, any base `g ≥ 2`) — **[St05]**, *J. Integer Seq.*
  **8** (2005), Art. 05.3.2.

(A third Stoll paper, **[St06]** — *On a problem of Erdős and Graham concerning digits*, *Acta Arith.*
**125** (2006), 89–100 — gives further/sharper results; it is not formalized here, and is not on the
critical path for #482.) The only genuinely new content in the formalization is **one fractional-part
inequality** (`0 ≤ {x} − √2{x/2} + √2/2 < 1`, eq (7) of arXiv:0902.4168); mathlib supplies `Int.fract`,
`irrational_sqrt_two`, `Real.digits`, and the rest.

## What is proven

`lake build` is green, with **zero `sorry` and zero custom axioms** (every theorem bottoms out at
`[propext, Classical.choice, Quot.sound]`).

- **Headline** — the Graham–Pollak √2 identity (`graham_pollak`), plus its restatement against
  mathlib's `Real.digits` and a concrete first-six-digits certificate.
- **Stoll's Theorem 3.2** — binary-digit identities for the GP-style `(α, l)` pairs: the general core
  plus all seven non-special pairs over their full ε-intervals. Pair 5 (`t₅ = √2` itself) is the special
  case and is formalized at `ε = ½` (the Graham–Pollak case); the detailed analysis of pair 5 is in
  [`NOTES-FOR-STOLL.md`](NOTES-FOR-STOLL.md).
- **Stoll's Corollary 3.3** — the unconditional title result, digits of `759250125·√2`
  (`cor33_unconditional`).

See [`STATUS.md`](STATUS.md) for the full theorem inventory + axiom ledger, and
[`NOTES-FOR-STOLL.md`](NOTES-FOR-STOLL.md) for the detailed pair-5 analysis, with exact-arithmetic
computations and reproduction scripts in [`tools/sandbox/`](tools/sandbox/).

## Acknowledgments

This formalization was carried out by Trevor Morris together with an AI assistant (Claude), which
composed the Lean proofs and the accompanying analysis.

Several supporting lemmas were proved with **Harmonic's Aristotle** auto-formalization system and then
re-checked by the Lean kernel — no result is trusted on Aristotle's (or any tool's) say-so; the
development is axiom-clean. The submitted problems are in [`tools/aristotle/`](tools/aristotle/) (see its
README). Aristotle closed the pair-5 Diophantine lemmas (e.g. `sqrt2_badly_approximable`,
`fract_two_mul`, `fract_sqrt2_pow_ne_half`, `pair5_band_branch`); the St05 Theorem 1.3 closed-form
induction (`thm13_closed`) it could not close, and that was proved by hand.

Built on [mathlib](https://github.com/leanprover-community/mathlib4).

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
