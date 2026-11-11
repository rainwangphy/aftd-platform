import AFTD.Prelude

/-!
# finite_packing_good_of_family_subset

Topic: graphs   Node: 5d8ba4a0341f

Provenance: helper lemma. Monotonicity step for simple_graph_packing_thirteen_stable_seed_good_packing.

If F is a subfamily of F-prime and a fixed packing has no member entirely covered by edges of F-prime that meet the packing in exactly one edge, then the same holds for F.
-/

theorem finite_packing_good_of_family_subset {E : Type} [DecidableEq E]
    (F F' P : Finset (Finset E)) (hFF' : F ⊆ F')
    (hgood : ∀ p ∈ P, ¬ p ⊆ ((F'.filter (fun t => (t ∩ P.biUnion id).card = 1)).biUnion id)) :
    ∀ p ∈ P, ¬ p ⊆ ((F.filter (fun t => (t ∩ P.biUnion id).card = 1)).biUnion id) := by
  intro p hp hsub
  apply hgood p hp
  intro e he
  obtain ⟨t,ht,het⟩ := Finset.mem_biUnion.mp (hsub he)
  obtain ⟨htF,htcard⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_filter.mpr ⟨hFF' htF,htcard⟩,het⟩
