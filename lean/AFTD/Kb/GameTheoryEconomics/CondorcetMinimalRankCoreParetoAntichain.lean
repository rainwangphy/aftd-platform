import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankDominatedVertexDelete
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_minimal_rank_core_pareto_antichain

Topic: social_choice   Node: 17904ffe7fb5

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. General rank-saturation and dominance-deletion route for the acyclic half-cover reformulation. Supporting structural lemmas only; no election bound or research novelty is claimed.

In a globally minimum induced S_k subset of a rank-compatible relation, with every vertex active somewhere, distinct vertices a and b with the activity signature of a contained in that of b must have an active index of a where b is ranked strictly before a. In particular, every same-signature cohort is a Pareto antichain; this supplies no cardinality bound.
-/

open Finset
set_option maxHeartbeats 4000000

theorem condorcet_minimal_rank_core_pareto_antichain
    {m n k : ℕ} (U : Fin n → Finset (Fin m))
    (p : Fin n → Fin m → ℕ) (B : Finset (Fin m))
    (hactive : ∀ a ∈ B, ∃ v, a ∈ U v)
    (hroot : ∀ J : Finset (Fin m), J ⊆ B → J.card ≤ k →
      ∃ r, r ∈ B ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation U p r c)
    (hmin : ∀ C : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ C → J.card ≤ k →
        ∃ r, r ∈ C ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation U p r c) →
      B.card ≤ C.card) :
    ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
      (∀ v, a ∈ U v → b ∈ U v) →
      ∃ v, a ∈ U v ∧ p v b < p v a := by
  intro a ha b hb hab hsub
  by_contra h
  push_neg at h
  have hdelete := condorcet_cover_rank_dominated_vertex_delete U p B a b ha hab
    (hactive a ha) hsub h hroot
  have hle := hmin (B.erase b) hdelete
  have hlt := card_erase_lt_of_mem hb
  omega
