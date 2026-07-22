# Erdős Problem #482 — moved to lean-gallery ➡️

This repository held a Lean 4 / mathlib formalization of
[Erdős problem #482](https://www.erdosproblems.com/482) — the Graham–Pollak identity, where the
recurrence `a₁ = 1`, `a(n+1) = ⌊√2·(aₙ + ½)⌋` reads off the binary expansion of `√2` — together with
Stoll's generalizations and a full base-`g` resolution.

**It now lives in [gotrevor/lean-gallery](https://github.com/gotrevor/lean-gallery).**

| What | Where |
|---|---|
| The Lean proof | [`LeanGallery/NumberTheory/Erdos482/`](https://github.com/gotrevor/lean-gallery/tree/main/LeanGallery/NumberTheory/Erdos482) |
| The headline theorems | `LeanGallery.NumberTheory.Erdos482.graham_pollak`, `…cor33_unconditional`, `…General.erdos482_resolution` |
| Writeups, the two errata, notes, reproduction scripts, Aristotle provenance, development record | [`docs/Erdos482/`](https://github.com/gotrevor/lean-gallery/tree/main/docs/Erdos482) |

Everything moved — 130 files, including every Aristotle problem submission and the session handoffs.
Nothing was dropped, and this repository's git history remains the original record.

## The two errata

Both were found *by formalizing*, and both are now in the gallery:

- [Two items in **Theorem 3.2**, pair `i = 5`](https://github.com/gotrevor/lean-gallery/blob/main/docs/Erdos482/STOLL-PAIR5-ERRATUM.md)
  of T. Stoll, *A fancy way to obtain the binary digits of 759250125√2*, **Amer. Math. Monthly 117**
  (2010), no. 7, 611–617.
- [**Theorem 3.1**](https://github.com/gotrevor/lean-gallery/blob/main/docs/Erdos482/notes/ST06-THM31-ERRATUM.md)
  of T. Stoll, *On a problem of Erdős and Graham concerning digits*, **Acta Arith. 125** (2006), 89–100.

Reported as findings about published mathematics, in the ordinary way one reports an erratum.

## Why move it

In the gallery the result is **maintained and independently checkable**, which it was not here:

- it builds against current Mathlib (this repo was pinned to an old toolchain and would eventually
  stop compiling, which reads to a visitor as a broken formalization);
- CI gates it on `#print axioms` asserting the exact triple `[propext, Classical.choice, Quot.sound]`;
- [`comparator`](https://github.com/leanprover/comparator) verifies the statements against a
  Mathlib-only rendering, replaying the proofs through the Lean kernel **and** the independent
  [`nanoda`](https://github.com/ammkrn/nanoda_lib) kernel inside a sandbox — so a stranger can check
  the result without trusting, or running, this author's code.

## Why the repo is still here

The URL is stable, and its git history holds the full development record. Both are worth more than
the disk they occupy.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris.
