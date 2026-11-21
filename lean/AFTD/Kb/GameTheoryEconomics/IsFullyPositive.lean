import AFTD.Prelude

/-!
# is_fully_positive

Topic: fair_division   Node: cefa9d53df13

Provenance: formalization of a published result. Source: arXiv:2611.25892, proof of Lemma 2.3

For n agents and m chores with cost matrix d : Fin n → Fin m → ℝ, chore c : Fin m is fully positive (is_fully_positive n m d c) if every agent i : Fin n assigns it strictly positive cost: ∀ i : Fin n, 0 < d i c.
-/

/-- A chore is fully positive if every agent assigns it strictly positive cost. -/
def is_fully_positive (n m : ℕ) (d : Fin n → Fin m → ℝ) (c : Fin m) : Prop := ∀ i : Fin n, 0 < d i c
