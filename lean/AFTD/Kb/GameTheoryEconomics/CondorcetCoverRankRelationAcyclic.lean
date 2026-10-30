import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_cover_rank_relation_acyclic

Topic: social_choice   Node: 72eabb816be6

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. General rank-saturation and dominance-deletion route for the acyclic half-cover reformulation. Supporting structural lemmas only; no election bound or research novelty is claimed.

Every activity set induces a well-founded relation in the rank-compatible relation, without any injectivity assumption on the ranks.
-/

open Finset
set_option maxHeartbeats 4000000

theorem condorcet_cover_rank_relation_acyclic {m n : ℕ}
    (U : Fin n → Finset (Fin m)) (p : Fin n → Fin m → ℕ) (v : Fin n) :
    WellFounded (fun a b : {a : Fin m // a ∈ U v} =>
      condorcet_cover_rank_relation U p a.val b.val) := by
  refine (measure (fun a : {a : Fin m // a ∈ U v} => p v a.val)).wf.mono ?_
  intro a b hab
  exact hab.2 v a.property b.property
