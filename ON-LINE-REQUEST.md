# ON-LINE-REQUEST — erdos-482

Networked (non-YOLO) host: fulfil by committing `ON-LINE-FINDINGS-<date>-<topic>.md`, deleting the
answered item below, and removing this file once nothing remains open.

## 2026-06-06 — St06 (Stoll, Acta Arithmetica 125 (2006), 89–100)

**Status:** St05 (J. Integer Seq. 8, 2005) is now FULLY formalized & axiom-clean (every theorem
Thm 1.1, 1.2 I+II, 1.3, Cor 1.1, 1.2). The next frontier is the sharper companion paper **St06**.

**Need:** the PDF/text of *On a problem of Erdős and Graham concerning digits* (Stoll, Acta Arith.
**125** (2006), 89–100, DOI [10.4064/aa125-1-8](https://doi.org/10.4064/aa125-1-8)) — earlier flagged
as IMPAN-outage-blocked. Specifically:
1. The exact statements of St06's main theorems (it is billed as "deeper/sharper" than St05 — what
   does it strengthen? uniqueness of the recurrence? a density/measure statement? bounds on the
   coefficients? the set of admissible `(a,b,ε)`?).
2. Its closed forms / coefficient formulas (verbatim), so we can numerically verify before formalizing
   (St05's printed pair-5 claim was *wrong* — same caution applies).
3. Whether St06 supersedes any St05 result we've already proved (so we don't duplicate).

**Why it unblocks:** with St05 done, St06 is the only remaining published content on #482; we cannot
fetch it here (no general egress, IMPAN was down). Even just the theorem statements let us state them
in Lean and start the prerequisite lemmas.
