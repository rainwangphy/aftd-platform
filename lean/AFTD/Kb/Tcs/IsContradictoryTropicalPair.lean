import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# is_contradictory_tropical_pair

Topic: proof_complexity   Node: dc084abeeab9

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 2.1

A tropical inequality between tropical polynomials represented by lists of terms P and Q (each term having rational coefficient and monomial CnfLit (Fin n) → ℕ) is contradictory if the zero monomial occurs in Q, and for every term (c_p, m) in P, m occurs in Q with a strictly smaller minimum coefficient: there exists a term in Q with monomial m whose coefficient is strictly less than the coefficient of every term in P with monomial m.
-/

/-- Condition that a tropical inequality P ≤ Q is contradictory. -/
def is_contradictory_tropical_pair (n : ℕ) (P Q : List (ℚ × (CnfLit (Fin n) → ℕ))) : Prop := (∃ t ∈ Q, ∀ l, t.2 l = 0) ∧
  (∀ (c_p : ℚ) (m : CnfLit (Fin n) → ℕ),
    (c_p, m) ∈ P →
    ∃ t_q ∈ Q, (∀ l, t_q.2 l = m l) ∧
      ∀ t_p ∈ P, (∀ l, t_p.2 l = m l) → t_q.1 < t_p.1)
