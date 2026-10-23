import AFTD.Prelude

/-!
# hn_graph

Topic: graphs   Node: 657f314b6a01

Provenance: formalization of a published result. Source: arXiv:2610.18636 Definition 3

For each natural number n, hn_graph n is the simple graph on the vertex set Fin (3 * n) defined via SimpleGraph.fromRel from the relation where u and v are related if (u.val < n - 1 and v.val ≥ n - 1) or (n - 1 ≤ u.val and u.val < 2 * n - 1 and 2 * n - 1 ≤ v.val and v.val < 3 * n - 1).
-/

/-- The competitor graph H_n on Fin (3 * n). -/
def hn_graph (n : ℕ) : SimpleGraph (Fin (3 * n)) :=
  SimpleGraph.fromRel fun u v =>
    (u.val < n - 1 ∧ v.val ≥ n - 1) ∨
    (n - 1 ≤ u.val ∧ u.val < 2 * n - 1 ∧ 2 * n - 1 ≤ v.val ∧ v.val < 3 * n - 1)
