# ON-LINE-REQUEST — Erdős #482

A networked host session fulfills these: commit an `ON-LINE-FINDINGS-<date>-<topic>.md`, delete the
answered item here, and remove this file once nothing is left open.

## 2026-06-06 — Stoll Theorem 3.2 + Corollary 3.3 (the BONUS)

**Source:** M. Stoll, *A fancy way to obtain the binary digits of 759250125√2*, arXiv:0902.4168.
The headline Graham–Pollak result (§4) is **fully formalized and axiom-clean** in this repo. The
remaining bonus needs the paper's precise statements, which are NOT reconstructable from memory:

1. **Theorem 3.2** — the table of **8 (α,β) pairs** (with l and γ=2α+β for each) and the exact
   parametrized recurrence `u₀ = ?`, `u(n+1) = ⌊√2·(uₙ + ?)⌋` that each pair uses. I need:
   - the explicit recurrence (initial value + the additive constant in terms of α,β),
   - the 8 rows of (α, β, l, γ) and which scaled irrational `c·√2` each extracts,
   - the precise digit-index statement (eqs (1)–(2) and (5)–(6) in general (α,β,l,γ) form).

2. **Corollary 3.3** — the exact statement for `759250125√2`, and the numeric facts it relies on
   (the paper mentions an `ε₆`-interval and bounds like `1 − π²/e⁴`); I need the precise inequality
   and which ε value / interval is used so I can discharge it with `norm_num`/interval arithmetic.

**Why this unblocks:** the general machinery is already in place — `crux` is the universal eq (7),
`eq8_general` is the full-interval eq (8). With the faithful parametrized statement I can replay the
`gp_pair` induction per pair. Without the paper text I cannot state Thm 3.2 faithfully (a mis-stated
index silently makes it wrong — same off-by-one I already had to correct in the headline).

A plain-text transcription of Thm 3.2 (statement + table) and Cor 3.3 (statement) suffices; the proof
is the same template I already formalized.
