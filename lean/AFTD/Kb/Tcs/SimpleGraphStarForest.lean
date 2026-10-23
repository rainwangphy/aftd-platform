import AFTD.Prelude

/-!
# simple_graph_star_forest

Topic: graphs   Node: 404b4fa5a002

Provenance: formalization of a published result. Source: arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Section 1: the star forest ⊔_{i=1}^q K_{1,n_i}

The star forest K_{1,n_1} ⊔ ... ⊔ K_{1,n_q}: component i has a centre (i, none) adjacent to its n_i leaves (i, some j), and there are no other edges.
-/

def simple_graph_star_forest (q : ℕ) (n : Fin q → ℕ) : SimpleGraph (Σ i : Fin q, Option (Fin (n i))) where
  Adj u v := u.1 = v.1 ∧ ((u.2 = none ∧ v.2 ≠ none) ∨ (u.2 ≠ none ∧ v.2 = none))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨fun _ h => by
    rcases h.2 with h | h
    · exact h.2 h.1
    · exact h.1 h.2⟩
