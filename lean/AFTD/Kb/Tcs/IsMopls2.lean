import AFTD.Prelude
import AFTD.Kb.Tcs.IsOpls2

/-!
# is_mopls2

Topic: combinatorics   Node: ce2ee3ab9c0b

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 1

A maximal pair of mutually orthogonal partial Latin squares of order n (2-MOPLS(n)) is a 2-OPLS(n) that cannot be extended to another 2-OPLS(n) by inserting any ordered pair into any empty cell.
-/

/-- Predicate for a maximal pair of mutually orthogonal partial Latin squares of order n. -/
def is_mopls2 {n : ℕ} (M : Fin n → Fin n → Option (Fin n × Fin n)) : Prop :=
  is_opls2 M ∧ ∀ (r c : Fin n), M r c = none → ∀ (p : Fin n × Fin n),
    ¬ is_opls2 (fun i j => if i = r ∧ j = c then some p else M i j)
