# ON-LINE-REQUEST

## 2026-06-13 — cubic / higher-degree self-referential digit recurrences (literature)

**Context.** This repo formalizes Stoll's Graham–Pollak digit results. The self-referential
phenomenon (the recurrence's own coefficient = the algebraic generator of the number whose digits it
reads, e.g. `u↦⌊√2(u+½)⌋` reads √2's binary digits) is now machine-checked to be a **base-2 /
quadratic** miracle: `src/Erdos482/General/SelfRefWall.lean` proves `selfref_crux_solvable_iff` —
`⌊√g(u+c)⌋` reads base-`g` digits (∀x crux) iff `g=2`. The genuinely-open frontier is the **cubic**
3-step analogue (`α=2^{1/3}`, `α³=2`, reading base 2 via a 3-step map), explored numerically and
found NEGATIVE for rational offset triples (`notes/CUBIC-EXPLORATION.md`): the bitstream from offset
`(1/6,1/3,4/3)` breaks at `j=64`; the recovered `W≈1.24986624` is not a clean `a+b·2^{1/3}+c·2^{2/3}`.

**What I need (any of):**
1. Has anyone studied **self-referential / coefficient-equals-generator floor recurrences** for
   **cubic (or higher-degree) algebraic irrationals** reading off their own base-`N` digits? Names,
   papers, or "open/folklore-negative". (Stoll's own papers, and the Erdős–Graham circle.)
2. Is there a known connection to **β-expansions / Pisot or Salem numbers** that would
   predict/explain the cubic failure (or give a positive construction with non-constant-modulus or
   field-valued offsets in `ℚ(2^{1/3})`)? `√2` is not Pisot, so the relevant structure is unclear.
3. Any reference establishing that elegant self-referential digit extraction is **impossible** beyond
   the quadratic/base-2 case — which would confirm `SelfRefWall` is the right general statement and
   that the cubic sub-questions (a)/(b) in `CUBIC-EXPLORATION.md` are genuinely closed-negative.

**Why it unblocks:** decides whether to invest a lap in formalizing a cubic *impossibility* theorem
(hard but tractable — analogue of `SelfRefWall`'s two-witness argument, scaled to the 3-step map) vs.
chasing a positive construction that the literature may already rule out.
