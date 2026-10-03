import AFTD.Prelude

/-!
# apx_paradox

Topic: social_choice   Node: 7365a602cfd4

Boolean test for a population paradox between two four-state profiles with given seat vectors.
-/

/-- Boolean population-paradox test between `(p, a)` and `(q, b)` for four states. -/
def apx_paradox (p a q b : Fin 4 → ℕ) : Bool :=
  (List.finRange 4).any fun i => (List.finRange 4).any fun j =>
    decide (i ≠ j) && decide (p i ≤ q i) && decide (q j ≤ p j) && decide (b i < a i) && decide (a j < b j)
