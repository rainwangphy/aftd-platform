import AFTD.Prelude
import AFTD.Kb.Tcs.IsPartialTransversal

/-!
# is_max_partial_transversal

Topic: combinatorics   Node: 7abb14e63a59

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

Given a dimension δ : ℕ, an ambient finset of cells S in Fin δ × Fin δ, and a finset of cells T in Fin δ × Fin δ, is_max_partial_transversal S T asserts that T is a partial transversal of S, and for every finset T' in Fin δ × Fin δ that is a partial transversal of S, the cardinality of T' is at most the cardinality of T.
-/

/-- A partial transversal T of S is maximum if no partial transversal of S has strictly greater cardinality. -/
def is_max_partial_transversal {δ : ℕ} (S : Finset (Fin δ × Fin δ)) (T : Finset (Fin δ × Fin δ)) : Prop :=
  is_partial_transversal S T ∧ ∀ T' : Finset (Fin δ × Fin δ), is_partial_transversal S T' → T'.card ≤ T.card
