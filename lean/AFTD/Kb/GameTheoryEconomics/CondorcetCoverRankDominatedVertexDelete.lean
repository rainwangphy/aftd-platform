import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_cover_rank_dominated_vertex_delete

Topic: social_choice   Node: 34404c313db4

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. General rank-saturation and dominance-deletion route for the acyclic half-cover reformulation. Supporting structural lemmas only; no election bound or research novelty is claimed.

Inside an induced S_k subset B of a rank-compatible relation, a vertex b can be deleted when a distinct vertex a in B is active somewhere, its activity signature is contained in that of b, and its rank is at most that of b on every index where a is active. The remaining induced subset retains S_k.
-/

open Finset
set_option maxHeartbeats 4000000

theorem condorcet_cover_rank_dominated_vertex_delete
    {m n k : ℕ} (U : Fin n → Finset (Fin m))
    (p : Fin n → Fin m → ℕ) (B : Finset (Fin m)) (a b : Fin m)
    (ha : a ∈ B) (hab : a ≠ b) (hne : ∃ v, a ∈ U v)
    (hsub : ∀ v, a ∈ U v → b ∈ U v)
    (hle : ∀ v, a ∈ U v → p v a ≤ p v b)
    (hroot : ∀ J : Finset (Fin m), J ⊆ B → J.card ≤ k →
      ∃ r, r ∈ B ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation U p r c) :
    ∀ J : Finset (Fin m), J ⊆ B.erase b → J.card ≤ k →
      ∃ r, r ∈ B.erase b ∧ r ∉ J ∧
        ∀ c ∈ J, condorcet_cover_rank_relation U p r c := by
  intro J hJ hcard
  obtain ⟨r,hrB,hrJ,hr⟩ := hroot J (hJ.trans (erase_subset _ _)) hcard
  by_cases hrb : r = b
  · subst r
    have haJ : a ∉ J := by
      intro haj
      obtain ⟨v,hv⟩ := hne
      have hlt := (hr a haj).2 v (hsub v hv) hv
      exact (not_lt_of_ge (hle v hv)) hlt
    refine ⟨a,mem_erase.mpr ⟨hab,ha⟩,haJ,?_⟩
    intro c hc
    refine ⟨fun heq => haJ (heq ▸ hc),?_⟩
    intro v hav hcv
    exact (hle v hav).trans_lt ((hr c hc).2 v (hsub v hav) hcv)
  · exact ⟨r,mem_erase.mpr ⟨hrb,hrB⟩,hrJ,hr⟩
