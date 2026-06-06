# PENDING_WORK — Erdős #482

Headline is COMPLETE and axiom-clean (see STATUS.md). One open item remains.

## Open item: BONUS — Stoll Theorem 3.2 (8 GP pairs) + Corollary 3.3 (759250125√2)

**Blocked on:** the paper's exact parametrized recurrence + the (α,β,l,γ) pair table + Cor 3.3's
numeric facts. Filed in `ON-LINE-REQUEST.md` (2026-06-06). DO NOT guess the parametrization — verified
this lap that even changing the additive constant ε away from 1/2 breaks the identities (e.g.
ε = 1−√2/2 gives u₁ = 1, not 2), so the generalization is subtle and must come from the paper.

### Three attack paths (once the paper text arrives)
1. **Replay `gp_pair` per pair.** The machinery is ready: `crux` is the universal eq (7),
   `eq8_general` is the full-interval eq (8). For each (α,β,l,γ) row, state the faithful pair of floor
   identities (the α-scaled analogue of `gp_pair`) and replay the `floorA`/`floorB` + induction
   skeleton in `Induction.lean`. Bridge to digits via the already-general `digits_eq_floor_sub`.
2. **Generalize `floorA`/`floorB` to (α,β,l,γ) first**, then instantiate all 8 pairs as corollaries —
   less duplication if the 8 proofs are truly the same template (the paper says they are).
3. **Cor 3.3 numerics** (`759250125√2`): isolate the single interval membership the paper uses
   (it mentions an ε₆-interval and a bound like `1 − π²/e⁴`); discharge with `norm_num` + mathlib's
   `Real.pi`/`Real.exp` bounds. Architect this as a standalone Aristotle job if the bounds are stiff.

### If still blocked on the paper next lap
- Harvest any `ON-LINE-FINDINGS-*.md` first.
- Keep the Aristotle loop alive (cross-checks / standalone sub-lemmas).
- The headline result is publishable as-is; the bonus is strictly additive.
