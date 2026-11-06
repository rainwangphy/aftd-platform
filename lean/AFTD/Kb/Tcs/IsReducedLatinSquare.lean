import AFTD.Prelude
import AFTD.Kb.Tcs.LatinSquareIs

/-!
# is_reduced_latin_square

Topic: combinatorics   Node: 509a316981c0

Provenance: formalization of a published result. Source: arXiv:2611.07118, Perfect Partitions of Regular Bipartite Graphs, Section 1.1

An n × n array R on Fin n is a reduced Latin square if it is a Latin square whose first row and first column are the identity permutation.
-/

/-- A reduced Latin square of order n: a Latin square whose first row and first column are the identity. -/
def is_reduced_latin_square {n : ℕ} [NeZero n] (R : Fin n → Fin n → Fin n) : Prop := latin_square_is R ∧ (∀ j, R 0 j = j) ∧ (∀ i, R i 0 = i)
