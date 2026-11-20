import AFTD.Prelude

/-!
# is_cycle_free_d_partition

Topic: graphs   Node: eaf5cd15602f

Provenance: formalization of a published result. Source: arXiv:2611.19473, Section 1

A cycle-free d-partition of the complete graph on a vertex set V is a family of d cycle-free (acyclic) subgraphs whose edge sets are pairwise disjoint and whose union is the complete graph.
-/

/-- Predicate asserting that a d-tuple of spanning subgraphs forms a cycle-free d-partition of the complete graph on 2d vertices. -/
def is_cycle_free_d_partition (d : ℕ) {V : Type*} (P : Fin d → SimpleGraph V) : Prop :=
  (∀ i, (P i).IsAcyclic) ∧
  (∀ i j, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) ∧
  (⋃ i, (P i).edgeSet) = (⊤ : SimpleGraph V).edgeSet
