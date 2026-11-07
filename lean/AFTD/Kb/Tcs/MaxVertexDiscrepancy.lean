import AFTD.Prelude

/-!
# max_vertex_discrepancy

Topic: online_algorithms   Node: 0afd126b8f60

Provenance: formalization of a published result. Source: arXiv:2611.00388 Sec 1.1, Online carpooling against an oblivious adversary

The maximum absolute discrepancy among all vertices for an integer discrepancy vector d on n vertices.
-/

/-- The supremum norm of an integer discrepancy vector on n vertices. -/
def max_vertex_discrepancy (n : ℕ) (d : Fin n → ℤ) : ℕ := Finset.univ.sup (fun v => (d v).natAbs)
