import AFTD.Prelude

/-!
# MaximalChainLowerSet

Topic: combinatorics   Node: 6c989f016051

Provenance: formalization of a published result. Source: arXiv:2611.26888 Section 2.1

A maximal chain in the lattice of order ideals J(P) of a finite poset P of size n is a sequence of n+1 order ideals from ∅ to P with each covering the preceding one.
-/

/-- A maximal chain in the lattice of order ideals J(P) of a finite poset P. -/
structure MaximalChainLowerSet (P : Type*) [PartialOrder P] [Fintype P] where
  chain : Fin (Fintype.card P + 1) → LowerSet P
  bot_eq : chain 0 = ⊥
  top_eq : chain (Fin.last (Fintype.card P)) = ⊤
  covBy : ∀ i : Fin (Fintype.card P), chain i.castSucc ⋖ chain i.succ
