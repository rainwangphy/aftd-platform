import AFTD.Prelude

/-!
# even_linked_double_star

Topic: combinatorics   Node: 7df27615eb6a

Provenance: formalization of a published result. Source: arXiv:2611.19632, Section 1

For natural numbers p, n, and m, the even-linked double star S_{2p}(n, m) is the simple graph on vertex set Fin(2p) ⊕ Fin(n) ⊕ Fin(m) whose edges consist of the path of length 2p - 1 on Fin(2p), edges joining 0 to each of the n leaves in Fin(n), and edges joining 2p - 1 to each of the m leaves in Fin(m).
-/

/-- The even-linked double star S_{2p}(n, m) with 2p path vertices, n leaves at the first endpoint, and m leaves at the second. -/
def even_linked_double_star (p n m : ℕ) : SimpleGraph (Fin (2 * p) ⊕ Fin n ⊕ Fin m) :=
  SimpleGraph.fromRel fun u v =>
    (∃ (i j : Fin (2 * p)), u = Sum.inl i ∧ v = Sum.inl j ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∨
    (∃ (i : Fin (2 * p)) (l : Fin n), i.val = 0 ∧
      ((u = Sum.inl i ∧ v = Sum.inr (Sum.inl l)) ∨ (u = Sum.inr (Sum.inl l) ∧ v = Sum.inl i))) ∨
    (∃ (i : Fin (2 * p)) (r : Fin m), i.val + 1 = 2 * p ∧
      ((u = Sum.inl i ∧ v = Sum.inr (Sum.inr r)) ∨ (u = Sum.inr (Sum.inr r) ∧ v = Sum.inl i)))
