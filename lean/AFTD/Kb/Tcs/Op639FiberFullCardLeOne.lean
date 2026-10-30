import AFTD.Prelude

/-!
# op_639_fiber_full_card_le_one

Topic: combinatorics   Node: d63f707fa801

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

In a 4-uniform hypergraph, if T has size 4, any edge satisfying e ∩ T = T must equal T, so there is at most 1 such edge.
-/

/-- At most one edge of a 4-uniform family can satisfy e ∩ T = T for a 4-element transversal T. -/
theorem op_639_fiber_full_card_le_one
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (hunif : ∀ e ∈ F, e.card = 4)
    (T : Finset V) (hT : T.card = 4) :
    (F.filter (fun e => e ∩ T = T)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro e f he hf
  simp only [Finset.mem_filter] at he hf
  have hTe : T ⊆ e := by
    rw [← Finset.inter_eq_right]
    exact he.2
  have he_card : e.card ≤ T.card := by rw [hunif e he.1, hT]
  have heT : e = T := (Finset.eq_of_subset_of_card_le hTe he_card).symm
  have hTf : T ⊆ f := by
    rw [← Finset.inter_eq_right]
    exact hf.2
  have hf_card : f.card ≤ T.card := by rw [hunif f hf.1, hT]
  have hfT : f = T := (Finset.eq_of_subset_of_card_le hTf hf_card).symm
  rw [heT, hfT]
