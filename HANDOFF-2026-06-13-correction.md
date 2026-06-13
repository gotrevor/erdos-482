# Handoff: Thm 3.4 faithfulness CORRECTED + self-referential wall formalized (SelfRefWall)

**Date**: 2026-06-13 (correction lap) · **Branch**: `st06` · **HEAD**: `b77f47d`

## 🎯 What this lap did (the prior "St06 COMPLETE" handoff was wrong)

The previous baton (`HANDOFF-2026-06-13-2255.md`) declared St06 complete with "no open obligation."
An **unharvested ON-LINE findings doc** overturned that: the repo's **Theorem 3.4** work formalized a
**swapped recurrence** — `ε` on the b-step, which is Theorem **3.3**'s placement. Stoll's actual 3.4
puts `ε` on the **a-step**. The prior lap's celebrated "Diophantine obstruction / only ε=½ works for
all w" was a *faithful proof of an unfaithful statement* (axiom-clean ≠ statement-faithful).

**Fixed, all axiom-clean (`#print axioms` = trust base only), build 🟢 8274 jobs:**
1. **Genuine Theorem 3.4 full interval** (`src/Erdos482/General/St06Thm34.lean`). The `su` recurrence
   def already had `ε` on the a-step (`su a b ε (1/2) m` IS Stoll's 3.4):
   - `st06_thm34_astep_eps` — a-step floor crux for **every** `ε ∈ ½ ± (m−l+½)/D₁`,
     `D₁=(2m+1)(2k+1)+2l`, uniform over all `t∈[1,2)` (NO Diophantine input). Endpoints = independent
     worst cases of `t∈[1,2)` and `2B−ts∈(−2,0]`, both binding at `t=1`.
   - `st06_thm34_{closed,digits,isBit,even_digits}_eps` — full closed forms + conclusions (1) & (2)
     for every ε in the interval. The genuine `t`-universal Theorem 3.4.
   - `st06_thm34_sqrt2_eps_nonhalf` — concrete **ε = 9/20 ≠ ½** reads √2's binary digits (witness the
     interval has teeth; for (m,l,k)=(1,1,0) the interval is [2/5,3/5)).
   - The old `ε`-on-b-step theorems (`bstep_value/band`, `band_fails_below/above_half`) are KEPT but
     re-labeled `[SWAPPED-VARIANT, NOT Thm 3.4]` as a documented contrast.
2. **Ground truth**: `tools/sandbox/st06_thm34_HOSTCHECK.py` (paper recurrence, 220-digit, to n=80)
   confirms the digit-correct ε range CONTAINS Stoll's printed interval in every case; the swapped
   recurrence collapses to ≈[0.49,0.50] (the spurious "only ε=½"). Old `verify.py` annotated.
3. Findings doc harvested → `archive/findings/ON-LINE-FINDINGS-2026-06-13-thm34.md`. STATUS.md +
   module header + CUBIC-EXPLORATION.md all corrected.

## 🆕 New mathematics — `src/Erdos482/General/SelfRefWall.lean` (beyond Stoll)

Engaging the "is the cubic generalization possible" frontier *structurally* instead of numerically,
proved the self-referential digit phenomenon is **exactly** the √2/base-2 miracle:
- `selfref_crux_fails_of_three_le` — for every integer `g ≥ 3` and ANY offset `c`, the `g`-analogue
  crux `0 ≤ {x} − √g·{x/g} + c·√g < 1` fails for some `x` (two explicit witnesses `x=g−1`, `x=1/2`
  pin `c` into the empty interval `[(g−1)/g, 1/g]`).
- `selfref_crux_solvable_iff` — for `g ≥ 2`: solvable (∃c ∀x) **iff `g=2`** (g=2 via `Erdos482.crux`).
- `selfref_crux_offset_unique` — for `g=2`, the offset is forced: `c = ½`.
- ⇒ `⌊√2·(u+½)⌋` is THE unique self-referential base-`g` digit recurrence — base AND offset forced.
  This explains the cubic wall structurally: even quadratic `√g` already dies for `g≥3` (digit range
  too wide); the cubic `2^{1/3}` 3-step map is a separate, still-open failure (3 floors can't align).

## 🤖 Aristotle
- `thm34astep` (`d9a743f9`) — **COMPLETE**, independently re-proved `st06_thm34_astep_eps`,
  axiom-clean. Cross-validates this lap's central a-step crux.
- `selfrefwall` (`8c772507`) — **was RUNNING at handoff** cross-validating
  `selfref_crux_fails_of_three_le`. Next lap: `aristotle show 8c772507`; if COMPLETE, it's confirmatory
  (already proven locally + axiom-clean). Then submit the next bounded lemma to keep one in flight.

## 🎬 Next actions
1. Poll/verify `selfrefwall` Aristotle job (confirmatory only).
2. **Open research frontier (blocked on web)**: cubic/higher-degree self-referential digit recurrences
   — `ON-LINE-REQUEST.md` (2026-06-13) asks for literature (β-expansions/Pisot, known impossibility).
   If findings arrive, decide whether to formalize a cubic *impossibility* (hard: 3-step map, nested
   floors of `2^{1/3}`, far harder than SelfRefWall's two-witness argument) or pursue a positive
   construction. Sub-questions (a)/(b) in `notes/CUBIC-EXPLORATION.md`.
3. Optional polish: top-level St06 showcase re-exporting the genuine Thm 3.4 + SelfRefWall.

## ⚠️ Gotchas
- DO NOT push (Trevor merges); commit every green build. Pre-commit hook runs full `lake build` (slow).
- Lesson of this lap: **`#print axioms` clean says NOTHING about statement-faithfulness.** When a repo
  claims an "obstruction / not-universal" result, check the recurrence matches the paper before trusting.
- The faithfulness sweep this lap was clean otherwise: Thm 3.3 is correct (ε on b-step IS 3.3's shape);
  pair 5 in `Stoll.lean` is genuinely Diophantine (different paper, arXiv:0902.4168) — both faithful.

## 📁 Key files
- `src/Erdos482/General/St06Thm34.lean` — genuine Thm 3.4 (`*_eps`) + re-labeled swapped contrast.
- `src/Erdos482/General/SelfRefWall.lean` — the self-referential characterization suite (NEW).
- `STATUS.md` axiom ledger · `notes/CUBIC-EXPLORATION.md` (updated) · `tools/sandbox/st06_thm34_HOSTCHECK.py`.

---
**→ Start next lap here: St06 is now genuinely complete AND faithful (Thm 3.4 corrected), plus a novel
self-referential-wall characterization. The only open frontier is the cubic research question, blocked
on `ON-LINE-REQUEST.md`. Verify the `selfrefwall` Aristotle job, then either act on findings or pursue
the cubic impossibility / a positive Pisot-base construction. Do NOT re-trust "COMPLETE" claims without
a faithfulness check.**
