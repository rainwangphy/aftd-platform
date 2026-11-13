import AFTD.Prelude

/-!
# opl2_filled_count

Topic: combinatorics   Node: e2a80ff39fb0

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 1

Given a natural number n and an n × n partial array of pairs M : Fin n → Fin n → Option (Fin n × Fin n), the number of filled cells opl2_filled_count M is the cardinality of the finset of indices (r, c) : Fin n × Fin n such that M r c is not none.
-/

/-- The number of filled cells F in an n × n partial array of pairs. -/
def opl2_filled_count {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => (M p.1 p.2).isSome)).card
