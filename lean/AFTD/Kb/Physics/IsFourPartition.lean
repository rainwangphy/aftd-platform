import AFTD.Prelude

/-!
# is_four_partition

Topic: quantum_mechanics   Node: 0df62f0e51d9

Provenance: formalization of a published result. Source: folklore

Given a finite type V with decidable equality and four finite subsets A, B, C, D : Finset V, is_four_partition A B C D is the proposition that A, B, C, D are pairwise disjoint and their union is the universal finset.
-/

/-- A four-partition of the vertices of a finite type, allowing empty parts. -/
def is_four_partition {V : Type*} [Fintype V] [DecidableEq V]
    (A B C D : Finset V) : Prop := Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧
  Disjoint B C ∧ Disjoint B D ∧ Disjoint C D ∧
  A ∪ B ∪ C ∪ D = Finset.univ
