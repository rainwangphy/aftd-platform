import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover

/-!
# condorcet_common_predecessor_neighborhood

Topic: social_choice   Node: 7bb63e4f8055

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural verification of the maximum-potential neighborhood route suggested in IN-380. Generalization of the existing acyclic-cover reduction, whose strict election definition is from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . No new election bound or research novelty is claimed.

In a finite relation in which every set of at most k+1 vertices has an outside common predecessor, the relation induced on the predecessors of any vertex has the analogous property for sets of at most k vertices.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_common_predecessor_neighborhood
    {V : Type*} [Fintype V] (R : V → V → Prop) (k : ℕ)
    (hroot : ∀ J : Finset V, J.card ≤ k+1 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) (b : V) :
    ∀ J : Finset {a : V // R a b}, J.card ≤ k →
      ∃ a : {a : V // R a b}, a ∉ J ∧ ∀ c ∈ J, R a.val c.val := by
  classical
  intro J hJ
  have hc : (insert b (J.image Subtype.val)).card ≤ k+1 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right (card_image_le.trans hJ) 1)
  obtain ⟨a, ha, har⟩ := hroot (insert b (J.image Subtype.val)) hc
  let a' : {a : V // R a b} := ⟨a,har b (mem_insert_self _ _)⟩
  refine ⟨a', ?_, ?_⟩
  · intro hmem
    exact ha (mem_insert_of_mem (mem_image.mpr ⟨a',hmem,rfl⟩))
  · intro c hc
    exact har c.val (mem_insert_of_mem (mem_image.mpr ⟨c,hc,rfl⟩))
