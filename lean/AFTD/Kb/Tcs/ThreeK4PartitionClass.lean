import AFTD.Prelude

/-!
# three_k4_partition_class

Topic: combinatorics   Node: b2924e0e0d16

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), proof of Theorem 1.1 (the classes of M₂)

The nine classes of the partition matroid M₂: in copy i the opposite pair a_i (edges 01, 23) is a class, and the classes {b_i⁺, c_{i+1}⁻} and {c_i⁺, b_{i+1}⁻} (indices mod 3) pair edges of consecutive copies.
-/

/-- Partition classes of the second matroid of arXiv:2610.07318, Theorem 1.1. -/
def three_k4_partition_class (x : Fin 3 × Fin 6) : Fin 9 :=
  ![⟨x.1, by omega⟩, ⟨x.1, by omega⟩, ⟨3 + x.1, by omega⟩,
    ⟨6 + (x.1 + 2 : Fin 3), by omega⟩, ⟨6 + x.1, by omega⟩, ⟨3 + (x.1 + 2 : Fin 3), by omega⟩] x.2
