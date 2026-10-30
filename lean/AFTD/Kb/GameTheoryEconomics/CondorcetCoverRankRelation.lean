import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover

/-!
# condorcet_cover_rank_relation

Topic: social_choice   Node: da33c86d0266

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. General rank-saturation and dominance-deletion route for the acyclic half-cover reformulation. Supporting structural lemmas only; no election bound or research novelty is claimed.

The loopless rank-compatible relation: an arrow a to b is permitted precisely when a differs from b and a has a strictly smaller natural-number rank than b in every acyclic-set index containing both vertices.
-/

open Finset
set_option maxHeartbeats 4000000

def condorcet_cover_rank_relation {m n : ℕ}
    (U : Fin n → Finset (Fin m)) (p : Fin n → Fin m → ℕ)
    (a b : Fin m) : Prop :=
  a ≠ b ∧ ∀ v, a ∈ U v → b ∈ U v → p v a < p v b
