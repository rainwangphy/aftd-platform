import AFTD.Prelude

/-!
# twin_star

Topic: graphs   Node: 6d485353930c

Provenance: formalization of a published result. Source: arXiv:2611.19473, Section 1

For any natural number d, the twin-star graph TS_d is the simple graph on vertex type Fin d ⊕ Fin d, where distinct vertices x and y are adjacent if and only if either: one vertex is Sum.inl i and the other is Sum.inr j with i.val = 0 and j.val = 0; or both vertices are in the left copy, Sum.inl i and Sum.inl j, with i.val = 0 or j.val = 0; or both vertices are in the right copy, Sum.inr i and Sum.inr j, with i.val = 0 or j.val = 0.
-/

/-- The twin-star graph TS_d on 2d vertices (Fin d ⊕ Fin d). -/
def twin_star (d : ℕ) : SimpleGraph (Fin d ⊕ Fin d) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl i, .inr j => i.val = 0 ∧ j.val = 0
    | .inl i, .inl j => i.val = 0 ∧ j.val ≠ 0
    | .inr i, .inr j => i.val = 0 ∧ j.val ≠ 0
    | _, _ => False
