import AFTD.Prelude

/-!
# opl2_col_freq

Topic: combinatorics   Node: 81284bd1d26a

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

Given a natural number n, an n × n partial array of pairs M : Fin n → Fin n → Option (Fin n × Fin n), and a column index c : Fin n, the column frequency opl2_col_freq M c is the cardinality of the finset of row indices r : Fin n such that M r c is not none.
-/

/-- The number of filled cells in column c of an n × n partial array of pairs. -/
def opl2_col_freq {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) (c : Fin n) : ℕ :=
  (Finset.univ.filter (fun r : Fin n => (M r c).isSome)).card
