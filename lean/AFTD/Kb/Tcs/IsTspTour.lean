import AFTD.Prelude

/-!
# is_tsp_tour

Topic: approximation   Node: 99c0c6e61dfc

Provenance: formalization of a published result. Source: arXiv:2611.09421 Section 1

A tour on a finite set V is a permutation σ of V that forms an n-cycle (it is a cycle and has full support).
-/

/-- A tour on a finite set V is a cyclic permutation of full support. -/
def is_tsp_tour {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) : Prop := σ.IsCycle ∧ σ.support = Finset.univ
