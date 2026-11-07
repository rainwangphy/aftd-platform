import AFTD.Prelude

/-!
# extremal_tree_vertex_bound

Topic: combinatorics   Node: 6c22493c7bbb

Provenance: formalization of a published result. Source: arXiv:2611.04184 Theorem 4.6 (Short permutation pattern waves: The complete length-five classification)

For integers C, q ≥ 0, the extremal vertex bound F_C(q) is defined by 2^q - 1 if q ≤ C, and (2^C - 1) + 2^C * (q - C) if q > C.
-/

/-- The extremal vertex bound F_C(q) for binary trees with child-subtree overlap at most C and at most q classes. -/
def extremal_tree_vertex_bound (C q : ℕ) : ℕ := if q ≤ C then 2 ^ q - 1 else (2 ^ C - 1) + 2 ^ C * (q - C)
