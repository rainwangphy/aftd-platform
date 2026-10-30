import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover

/-!
# condorcet_acyclic_cover_rank_saturation

Topic: social_choice   Node: 6a1e45fe8316

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. General rank-saturation and dominance-deletion route for the acyclic half-cover reformulation. Supporting structural lemmas only; no election bound or research novelty is claimed.

For any finite relation with the outside common predecessor property for sets of at most k vertices and any finite acyclic cover family, there are injective natural-number rankings such that the rank-compatible relation contains every nonloop original arrow and retains the k-predecessor property on the same vertices. Memberships and their multiplicities are unchanged.
-/

open Finset
set_option maxHeartbeats 4000000

theorem condorcet_acyclic_cover_rank_saturation
    (m n k : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) :
    ∃ p : Fin n → Fin m → ℕ,
      (∀ v, Function.Injective (p v)) ∧
      (∀ a b, a ≠ b → R a b → condorcet_cover_rank_relation U p a b) ∧
      (∀ J : Finset (Fin m), J.card ≤ k →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_cover_rank_relation U p a b) := by
  classical
  have hp : ∀ v, ∃ σ : Equiv.Perm (Fin m),
      ∀ a b, a ∈ U v → R a b → σ a < σ b := by
    intro v
    obtain ⟨σ,hσ⟩ := condorcet_acyclic_cover_ranking_of_wellFounded m
      (fun a b => a ∈ U v ∧ R a b)
      (condorcet_acyclic_cover_wellFounded_sources R {a | a ∈ U v} (hU v))
    exact ⟨σ,fun a b ha hab => hσ a b ⟨ha,hab⟩⟩
  choose σ hσ using hp
  let p : Fin n → Fin m → ℕ := fun v a => (σ v a).val
  have hR : ∀ a b, a ≠ b → R a b → condorcet_cover_rank_relation U p a b := by
    intro a b hab h
    exact ⟨hab,fun v ha _ => hσ v a b ha h⟩
  refine ⟨p,?_,hR,?_⟩
  · intro v a b hab
    exact (σ v).injective (Fin.ext hab)
  · intro J hJ
    obtain ⟨a,ha,har⟩ := hroot J hJ
    exact ⟨a,ha,fun b hb => hR a b (fun heq => ha (heq ▸ hb)) (har b hb)⟩
