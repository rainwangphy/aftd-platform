import AFTD.Prelude

/-!
# condorcet_minimal_predecessor_undominated_extension

Topic: social_choice   Node: be06588a7daa

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Constructive completion of the minimal-core incidence argument developed in this session; all four proofs were scratch-checked together in CanonicalAndTransport3.log. General supporting route lemmas, not a new election bound or a research novelty claim.

For every natural k, a finite relation globally minimal under induced restriction among S_k relations has an undominated set of exactly k+1 vertices. Thus its canonical family of missing (k+1)-sets is nonempty. No irreflexivity or positive-k hypothesis is needed.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_minimal_predecessor_undominated_extension
    (m k : ℕ) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ) :
    ∃ T : Finset (Fin m), T.card = k+1 ∧
      ¬∃ a, a∉T ∧ ∀ b∈T,R a b := by
  classical
  by_contra! h
  have hstrong : ∀ J : Finset (Fin m), J.card ≤ k+1 →
      ∃ a, a∉J ∧ ∀ b∈J,R a b := by
    intro J hJ
    by_cases hJk : J.card ≤ k
    · exact hroot J hJk
    · exact h J (by omega)
  obtain ⟨c,_,_⟩ := hroot ∅ (by simp)
  have heq : univ.erase c = (univ : Finset (Fin m)) := by
    apply hminimal
    intro J hJC hJ
    obtain ⟨a,ha,har⟩ := hstrong (insert c J)
      ((card_insert_le _ _).trans (by omega))
    have hac : a≠c := fun h => ha (h ▸ mem_insert_self c J)
    exact ⟨a,mem_erase.mpr ⟨hac,mem_univ _⟩,
      fun h => ha (mem_insert_of_mem h),fun b hb => har b (mem_insert_of_mem hb)⟩
  have hmem : c∈(univ : Finset (Fin m)).erase c := heq.symm ▸ mem_univ c
  exact (mem_erase.mp hmem).1 rfl
