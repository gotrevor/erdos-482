# HANDOFF — Erdős #482 (Graham–Pollak √2 binary digits) — Step 2 of 2

**Read `SETUP.md` first** (Step 1: repo + mathlib scaffold). This doc is the **math attack plan** each
fresh `lean-treadmill` lap resumes from. Target: a complete, **axiom-clean** formalization of the
Graham–Pollak identity. Estimate: **~2–3 sessions** for the headline (no machinery wall — this is the
EASY tail; comparable to #403 but *easier*, since the full modern proof is in hand, no lost-proof
reconstruction). Selected as the top target out of the [[erdos-formalization-hunt]] batch-2 deep-dive
(GREEN, conf ~83%).

## What we're proving

`u 0 = 1`, `u(n+1) = ⌊√2·(u n + ½)⌋`. Then **`d_n := u(2n+1) − 2·u(2n−1)` is the n-th binary digit of
√2** (`√2 = 1.0110101…₂`). Erdős also asks to "generalize to other algebraic numbers" — that half is an
**open research direction, NOT a theorem**; do not chase it. The formalizable HEADLINE is the concrete
GP identity. **Free bonus** worth grabbing after the headline: Stoll's Theorem 3.2 (8 GP pairs, same
proof parameterized) + Cor 3.3 (binary digits of `759250125√2`).

**Source (in hand, free):** Stoll, *A fancy way to obtain the binary digits of 759250125√2*,
[arXiv:0902.4168](https://arxiv.org/abs/0902.4168) — §4 has the complete proof. Orig.: Graham–Pollak,
Math. Mag. 43 (1970) 143–145.

## The proof (Stoll §4, specialized to GP: α=β=1, l=1, γ=2α+β=3, t=√2−1)

Induction on `k ≥ l+2 = 3` proving two floor identities:
- **(5)** `u(2k)   = ⌊t·2^{k−2}⌋ + γ·2^{k−l−2}`  =  `⌊√2·2^{k−2}⌋ + 3·2^{k−3}` for GP
- **(6)** `u(2k+1) = ⌊t·2^{k−1}⌋ + 2^k`

From (5)+(6): `u(2k+1) − 2u(2k−1) = ⌊t·2^{k−1}⌋ − 2⌊t·2^{k−2}⌋` = the k-th binary digit of `t`. ∎
(modulo finitely many small-k base cases `k ∈ {0,1}`, checked by `decide`/`norm_num`).

Each induction step is ONE floor identity reducing to ONE fractional-part inequality:
- **even step (5)→(6):** collapses (via `γ−β=2α`, `α+β=2^{l+1}`) to **eq (7)**:
  `0 ≤ {α√2·2^{k−l−1}} − √2·{α√2·2^{k−l−2}} + √2/2 < 1` — an instance of the **crux** below (α=1).
- **odd step (6)→(5):** collapses to **eq (8)**: `0 ≤ (1−√2){α√2·2^{k−l−1}} + √2·ε < 1`, true for
  `1−√2/2 ≤ ε < √2/2` (ε=½ qualifies — a one-line interval check).

### THE CRUX (do this FIRST — it's the whole proof in miniature, de-risks everything)
**`crux (x : ℝ) : 0 ≤ {x} − √2·{x/2} + √2/2 < 1`** (`Crux.lean`). Proof:
case-split on parity of `⌊x⌋`, giving the fract relation `{x} = 2{x/2}` (⌊x⌋ even) or `{x} = 2{x/2} − 1`
(⌊x⌋ odd):
- **Case even:** expr `= (2−√2){x/2} + √2/2 ∈ [√2/2, 2−√2/2) ⊂ [0,1)`.
- **Case odd:** `{x} ≥ 0 ⟹ {x/2} ≥ ½`; expr `= (2−√2){x/2} − 1 + √2/2`, low end `= 0` at `{x/2}=½`,
  high end `< 1`. Both land in `[0,1)`.
Discharge with `nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Int.fract_nonneg x, Int.fract_lt_one x, …]`
plus `1 < √2 < 3/2` facts. Needs a small **fract-of-x vs fract-of-x/2 parity helper** (not in mathlib).

## mathlib handles (all present in v4.29.1 unless marked MUST-BUILD)

- **Floor/fract:** `Int.fract`, `Int.fract_nonneg`, `Int.fract_lt_one`, `Int.self_sub_floor_eq_fract`,
  `Int.floor_intCast_add` / `Int.floor_add_int` (pull integer `2^k`, `γ·2^…` out of floors),
  `Int.floor_eq_iff` (the shape of every step goal: `⌊a⌋ = z ↔ z ≤ a < z+1`), `Int.fract_add_intCast`.
- **√2:** `Real.sq_sqrt` (√2²=2), `Real.lt_sqrt`/`Real.sqrt_lt'` (for `1<√2<3/2`), `irrational_sqrt_two`
  (only needed to rule out the dyadic-tail ambiguity when bridging to `Real.digits`; NOT for the pure
  floor identity).
- **ℕ↔ℤ floor** (sequence is ℕ-valued, proof cleaner over ℤ/ℝ): `Int.natCast_floor_eq_floor`, `Int.floor_toNat`.
- **Digit notion:** `Real.digits` (`Mathlib/Analysis/Real/OfDigits.lean`, `fun i ↦ Fin.ofNat 2 ⌊x·2^{i+1}⌋₊`).
- **MUST-BUILD (3 small items, none a wall):** (1) `crux` (~40–80 lines); (2) the fract-parity helper;
  (3) the `binDigit ↔ Real.digits` bridge (~30–60 lines, skippable for a self-contained headline but do
  it for publishable).

## Lap order (each lap = one green checkpoint)

1. **`crux`** in `Crux.lean` (the parity helper + the inequality). ← START HERE.
2. **(5)/(6)** by `Nat.le_induction` from `k=3` in `Induction.lean`, each step = `Int.floor_eq_iff` +
   `crux` + ring/floor arithmetic; the odd step needs the eq-(8) interval check for ε=½.
3. **base cases** `k ∈ {0,1}` (`decide`/`norm_num` on the first ~5 `u`-terms).
4. **`graham_pollak`** headline corollary (`Main.lean`) from (5)+(6).
5. **`Real.digits` bridge** (`Digits.lean`) + restate headline canonically → publishable.
6. **BONUS:** Stoll Thm 3.2 (8-pair table, per-pair (α,β,l,γ)) + Cor 3.3 (`759250125√2`; needs e/π
   numeric bounds for `1−π²/e⁴ ∈ ξ₆-interval`). Same proof template.

## Gotchas (earned, flag up front)

- **Base index is `k = l+2 = 3`** — the off-by-some on where induction starts is the #1 time-sink. Small-k
  cases are checked directly, not by the recurrence.
- **Do the math over ℝ/ℤ, bridge to the ℕ sequence** with `Int.natCast_floor_eq_floor` — don't fight ℕ subtraction.
- **`u` must be `noncomputable`** (`Real.sqrt`). `decide` on base cases works through the floor of explicit reals.
- **No `native_decide` needed and none wanted** (kernel-pure target, like #403). `#print axioms graham_pollak`
  should end at `[propext, Classical.choice, Quot.sound]`.
- **Faithfulness first:** before pouring effort down, confirm the headline `binDigit`/index form matches Stoll
  eqs (1)–(2) exactly (the statement is ~10 lines; a mis-stated digit index silently makes it wrong). See
  [[faithfulness-not-fluency]].
- **No scope-creep** into "all algebraic numbers" (open). Stoll Thm 3.2 IS in scope (free bonus).

## Doctrine + corpus pointers (for box laps — cwd=repo, so KB is NOT auto-loaded)

- KB reference corpus: `~/personal/claude/knowledge/core/projects/lean-journey/reference/` —
  `ls` + `grep` it for tactic gotchas / mathlib facts before re-fighting a known one.
- Axiom doctrine: this is a 🟢 finite/elementary target — drive to **ZERO custom axioms** (no deep-axiom
  excuse applies here; there's no wall). `feedback_axiom_discharge_doctrine.md`.
- Commit gate: in-repo `.githooks/pre-commit` (green `lake build` before commit). `STATUS.md` convention
  (axiom ledger, refresh each review lap) per [[lean-repo-status-md-overview-convention]].

## Treadmill launch (host)

After `SETUP.md` is done (skeleton green-with-sorries + pushed + box build confirmed):
```bash
lean-treadmill erdos-482 --effort high          # unbounded; one fresh c-yolo box lap per /handoff
# stop with:  lean-treadmill stop erdos-482      (NOT /handoff — that only ends the current lap)
# watch:      lean-treadmill list
```
First lap resumes from this doc → attacks `crux`. Auto-caffeinates; keep on AC + external display.

## Status

**Skeleton only — all `sorry`.** No lap has run. First green checkpoint = `crux`. Related:
[[erdos-403]] (the published sibling + repo template), [[erdos-formalization-hunt]] (selection + the
batch-2 deep-dive that picked this), [[lean-yolo-box]] / [[lean-treadmill]] (the runner).
