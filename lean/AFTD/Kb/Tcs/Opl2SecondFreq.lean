import AFTD.Prelude

/-!
# opl2_second_freq

Topic: combinatorics   Node: 8d2687ef7544

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

Given a natural number n, an n × n partial array of pairs M : Fin n → Fin n → Option (Fin n × Fin n), and an element y : Fin n, the second entry frequency opl2_second_freq M y is the cardinality of the finset of cell indices (r, c) : Fin n × Fin n such that (M r c).map Prod.snd = some y.
-/

/-- The number of occurrences of y as a second entry in an n × n partial array of pairs. -/
def opl2_second_freq {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) (y : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => (M p.1 p.2).map Prod.snd = some y)).card
