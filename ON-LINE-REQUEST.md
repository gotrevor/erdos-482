# On-line requests (need open web / the St06 PDF)

> **NOTE (2026-06-13): both St06 PDF worries are now NON-BLOCKING.**
> • **Cor 3.5 CLOSED without the PDF** — the "exact index convention" worry was illusory. The recurrence
>   reads off the digits of `r·√2` (the Beatty real `r·α`); Stoll's printed `w`-table is just a mantissa
>   renormalization of the same digit string. See `St06Cor35.lean` (`st06_cor35`).
> • **Thm 3.4 RESOLVED honestly** — we machine-checked the full interval is NOT t-universal
>   (`st06_thm34_band_fails_below_half`/`_above_half`: the d=0/d=1 boundary branches force ε=½). ε=½ is
>   the proven ceiling. The request below is now only a *curiosity* (does Stoll claim a per-`w`
>   Diophantine interval, or is the printed interval a transcription artifact?) — answer either way does
>   not change our formalization. Fulfil only if convenient.

## 2026-06-13 — Stoll [St06] Theorem 3.4 exact statement + ε-interval

**Source.** T. Stoll, *On a problem of Erdős and Graham concerning digits*, Acta Arith. 125 (2006),
89–100, **Theorem 3.4** (the second binary `g=2` family). The repo's transcription
(`notes/ST06-PLAN.md`) is incomplete (upper ε-bound shown as "(…)") and Stoll's transcriptions have a
known prior error (the Thm 3.1 `+1`, and the pair-5 interval was essentially false beyond ε=½).

**What I need (and why).** I derived Thm 3.4's closed forms and cruxes (see
`notes/ST06-THM34-FINDINGS.md`). My analysis shows the printed k-dependent interval
`½ − (m−l+½)/((2k+1)(2m+1)+2l) ≤ ε < ½ + (…)` is **NOT t-universal**: the b-step's two digit-branches
meet at ε=½, so for arbitrary `w` only ε=½ works for all `n` (the narrow band seen for `w=√2` is
Diophantine, the pair-5 phenomenon). I have formalized the honest **ε=½** case (t-universal).

Please report from the PDF: (1) Thm 3.4's exact hypotheses and the **exact** ε-interval (both
endpoints, open/closed); (2) whether Stoll states it per-`w` (with `t` fixed) or claims t-universality;
(3) the structure of his proof of the ε-step for 3.4 (does it use a Diophantine property of `t`?). This
tells me whether the full interval is a genuine theorem (per-w) or a transcription artifact, so I know
whether to chase it or rest on the ε=½ formalization. Same question shape as the pair-5 erratum.
