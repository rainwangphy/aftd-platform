import AFTD.Prelude

/-!
# opl2_first_freq

Topic: combinatorics   Node: 23646e7ce396

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

Given a natural number n, an n × n partial array of pairs M : Fin n → Fin n → Option (Fin n × Fin n), and an element x : Fin n, the first entry frequency opl2_first_freq M x is the cardinality of the finset of cell indices (r, c) : Fin n × Fin n such that (M r c).map Prod.fst = some x.
-/

/-- The number of occurrences of x as a first entry in an n × n partial array of pairs. -/
def opl2_first_freq {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) (x : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => (M p.1 p.2).map Prod.fst = some x)).card
