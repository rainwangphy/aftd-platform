import AFTD.Prelude
import AFTD.Kb.Tcs.PosetSortingMap
import AFTD.Kb.Tcs.BraidAut
import AFTD.Kb.Tcs.PosetSortingMapIntertwineIff

/-!
# braid_aut_poset_sorting_map

Topic: combinatorics   Node: 12d1d213d56e

Provenance: helper lemma. Step of arXiv:2611.15540, Theorem A (Theorem 2.1 and Corollary 2.2)

A permutation σ of a partially ordered set P lies in Aut(P,R_P) iff σ is (the underlying permutation of) an order automorphism of P.
-/

theorem braid_aut_poset_sorting_map (P : Type*) [PartialOrder P] (σ : Equiv.Perm P) :
    σ ∈ braid_aut (poset_sorting_map P) ↔ ∃ f : P ≃o P, f.toEquiv = σ := by
  change Prod.map σ σ ∘ _ = _ ↔ _
  rw [poset_sorting_map_intertwine_iff]
  constructor
  · intro hlt
    refine ⟨⟨σ, fun {a b} => ?_⟩, rfl⟩
    simp only [le_iff_lt_or_eq, hlt, σ.injective.eq_iff]
  · rintro ⟨f, rfl⟩ x y
    exact f.lt_iff_lt
