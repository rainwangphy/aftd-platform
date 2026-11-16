import AFTD.Prelude
import AFTD.Kb.Tcs.SignedRelation

/-!
# sign_chamber

Topic: combinatorics   Node: 1c36ad9fe1fb

Provenance: formalization of a published result. Source: arXiv:2611.17360 Definition 2.1

For any natural number n, sign_chamber n is the set of vectors x : Fin n → ℝ such that 1 ≤ signed_relation n (j.val + 1) x for all j : Fin n.
-/

/-- The sign chamber of vectors in Fin n → ℝ satisfying all signed relations. -/
def sign_chamber (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ j : Fin n, 1 ≤ signed_relation n (j.val + 1) x}
