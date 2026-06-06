# Erratum / caveat: Stoll arXiv:0902.4168, Theorem 3.2, pair i=5 (t₅=√2)

**DURABLE NOTE — keep, do not archive.** This records two problems in Stoll's paper that directly
shape how pair 5 should (and should not) be formalized here. Full evidence + scripts:
`ON-LINE-FINDINGS-2026-06-06-pair5.md` (root, or `archive/findings/` after harvest).

## 1. Typo in the pair-5 closed form (certain)
The paper prints, for i=5:  `v_{2k} = ⌊t₅·2^{k−2}⌋ + 2^{k−2}`.
This is **wrong** (gives v₂=0.5, v₄=2; true v₄=4). The correct formula is
> `v_{2k} = ⌊√2·2^{k−1}⌋ + 2^{k−1}`,  `v_{2k+1} = ⌊√2·2^{k−1}⌋ + 2^k`  (k ≥ 1),
both sharing the floor `⌊√2·2^{k−1}⌋`. (`v_{2k+1}` is correct as printed.) Verified by exact
integer arithmetic.

## 2. The pair-5 interval claim is too wide (substantive — not just a typo)
Thm 3.2 / remark (b) claims the digits of √2 are obtained for **any** ε in
`[309/2·√2−218, 1296121037/2·√2−916495974) ≈ [0.4959953, 0.5012400)`.
**False as an "all-n" statement.** Exact computation: at the *included* lower endpoint
ε=ξ₁,₅ the digit claim **fails at n=280**; the true admissible ε-set shrinks toward `{½}` as the
digit-horizon grows (governed by `{√2·2^m} → ½`, i.e. the base-2 normality of √2 — the very
connection Stoll flags in remark (d) but never applies to pair 5). Stoll's endpoints are the
**small-horizon** extremes (m≲28), inherited from the pair-4/pair-6 boundaries; he then wrongly
assumed the whole leftover gap is pair-5 territory. Cross-check: pairs 1,2,4,6,8 (eq-8 uniform) DO
hold over their full intervals to n=1500 with the same machinery — only pair 5 fails.

## Consequence for this repo
Pair 5 (digits of √2) is a genuine theorem **only at ε=½** (original Graham–Pollak), where the
ε-step is exactly the universal `crux` `0≤{x}−√2{x/2}+√2/2<1`. That is the case to formalize.
**Do not state/prove pair 5 over the open interval** — it is not an elementary theorem (it is
open-Diophantine / normality-flavored) and the stated interval is demonstrably wrong. A full
Theorem-3.2 formalization should scope pair 5 to ε=½ and cite this note.
