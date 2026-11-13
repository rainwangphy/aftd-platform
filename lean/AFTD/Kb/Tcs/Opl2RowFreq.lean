import AFTD.Prelude

/-!
# opl2_row_freq

Topic: combinatorics   Node: 835b08610a06

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

Given a natural number n, an n × n partial array of pairs M : Fin n → Fin n → Option (Fin n × Fin n), and a row index r : Fin n, the row frequency opl2_row_freq M r is the cardinality of the finset of column indices c : Fin n such that M r c is not none.
-/

/-- The number of filled cells in row r of an n × n partial array of pairs. -/
def opl2_row_freq {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) (r : Fin n) : ℕ :=
  (Finset.univ.filter (fun c : Fin n => (M r c).isSome)).card
