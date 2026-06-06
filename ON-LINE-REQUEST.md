# ON-LINE-REQUEST — Erdős #482 / Stoll

Networked host: please fulfill, commit an `ON-LINE-FINDINGS-<date>-pair5.md`, and delete this item.

## 2026-06-06 — Stoll's pair 5 (i=5, t₅=√2, β=0) FULL proof of Theorem 3.2

**Source:** M. Stoll, *A fancy way to obtain the binary digits of 759250125√2*, arXiv:0902.4168,
Section 4 (the proof of Theorem 3.2), specifically the **pair `i = 5`** (the special `t₅ = √2`,
`β = 0` case, excluded from the index set `I`).

**What I need (verbatim, not paraphrase):**
1. The exact statement Stoll proves for `i=5` over its ε-interval `[309/2·√2−218, 1296121037/2·√2−916495974)`
   — the analogue of eqs (5)/(6) for `t₅=√2`. (The transcription in
   `archive/findings/ON-LINE-FINDINGS-2026-06-06-stoll-thm32-cor33.md` gives
   `v_{2k}=⌊√2·2^{k−2}⌋+2^{k−2}`, `v_{2k+1}=⌊√2·2^{k−1}⌋+2^k`, but these **disagree with the actual
   recurrence**: they predict `v_4 = vv 3 = 2` whereas the true value is `4`. So either the
   transcription is wrong or the indexing differs — I need the correct eqs.)
2. **The key step**: how does Stoll show the `ε`-step (the even-index recurrence step) lands correctly
   for *all* `ε` in the interval, given that the per-step bound is NOT uniform in `ε`? My analysis
   (numerically confirmed) is that the ε-step requires `{√2·2^j}` to avoid a forbidden sub-band of
   `[0,1)` for all `j` — an infinitary property of √2's binary digits. Does Stoll use a
   continued-fraction / Diophantine bound on √2, an equidistribution argument, or some finite
   reduction I'm missing? This is the crux that unblocks the Lean formalization of pair 5.

**Why it unblocks me:** pairs 1–4,6,7,8 are formalized (full intervals, axiom-clean) via a uniform
`crux`/`eq8_general` induction. Pair 5 does NOT fit that template (its ε-step bracket is
`{x}−√2{x/2}+√2ε`, not `eq8`'s `(1−√2){y}+√2ε`). Knowing Stoll's actual argument tells me whether
pair 5 needs new Diophantine machinery or has an elementary finite proof.
