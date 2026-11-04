import AFTD.Prelude

/-!
# finset_transversal_number

Topic: graphs   Node: 8e3f36e710ea

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 2, line 138

The transversal number of a collection C of subsets of a finite set V is the minimum cardinality of a subset T of V that intersects every set S in C.
-/

/-- The transversal number of a collection of subsets is the minimum cardinality of a set intersecting each member. -/
noncomputable def finset_transversal_number {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V)) : ℕ := sInf { k : ℕ | ∃ T : Finset V, (∀ S ∈ C, (T ∩ S).Nonempty) ∧ T.card = k }
