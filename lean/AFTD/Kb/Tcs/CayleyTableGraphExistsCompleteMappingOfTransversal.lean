import AFTD.Prelude
import AFTD.Kb.Tcs.CayleyTableGraph
import AFTD.Kb.Tcs.GroupIsCompleteMapping

/-!
# cayley_table_graph_exists_complete_mapping_of_transversal

Topic: combinatorics   Node: 15bbccdd16f6

Provenance: formalization of a published result. Source: arXiv:2611.13274 Theorem 2.12

If the Cayley table graph of a finite group G contains a transversal of cardinality |G|, then G admits a complete mapping.
-/

/-- A transversal of cardinality |G| in the Cayley table graph gives a complete mapping of G. -/
theorem cayley_table_graph_exists_complete_mapping_of_transversal
    (G : Type*) [Group G] [Fintype G] (s : Finset (G × G))
    (hindep : (cayley_table_graph G).IsIndepSet (s : Set (G × G)))
    (hcard : s.card = Fintype.card G) :
    ∃ θ : G → G, group_is_complete_mapping θ := by
  classical
  have hfst : ∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q := by
    intro p hp q hq h
    by_contra hne
    exact hindep hp hq hne ⟨hne, Or.inl h⟩
  have hsnd : ∀ p ∈ s, ∀ q ∈ s, p.2 = q.2 → p = q := by
    intro p hp q hq h
    by_contra hne
    exact hindep hp hq hne ⟨hne, Or.inr (Or.inl h)⟩
  have himg : s.image (fun p : G × G => p.1) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn, hcard]
    intro p hp q hq h
    exact hfst p hp q hq h
  have hex : ∀ x : G, ∃ y : G, (x, y) ∈ s := by
    intro x
    have : x ∈ s.image (fun p : G × G => p.1) := by rw [himg]; simp
    rw [Finset.mem_image] at this
    obtain ⟨p, hp, hpx⟩ := this
    exact ⟨p.2, by rw [← hpx]; exact hp⟩
  let θ : G → G := fun x => if h : ∃ y, (x, y) ∈ s then h.choose else 1
  have hmem : ∀ x : G, (x, θ x) ∈ s := by
    intro x
    have h := hex x
    simp only [θ]
    rw [dif_pos h]
    exact h.choose_spec
  have hθinj : Function.Injective θ := by
    intro x y hxy
    have hp := hmem x
    have hq := hmem y
    have hpq : (x, θ x) = (y, θ y) := hsnd _ hp _ hq hxy
    have : (x, θ x).1 = (y, θ y).1 := by rw [hpq]
    simpa using this
  have hψinj : Function.Injective (fun x => x * θ x) := by
    intro x y hxy
    by_contra hne
    have hp := hmem x
    have hq := hmem y
    have hpq : (x, θ x) ≠ (y, θ y) := by
      intro h
      exact hne (Prod.ext_iff.mp h).1
    exact hindep hp hq hpq ⟨hpq, Or.inr (Or.inr hxy)⟩
  refine ⟨θ, hθinj.bijective_of_finite, hψinj.bijective_of_finite⟩
