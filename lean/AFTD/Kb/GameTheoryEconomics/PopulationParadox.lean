import AFTD.Prelude

/-!
# population_paradox

Topic: social_choice   Node: d83c70380b94

A population paradox between (p, h) and (p', h'): two states i != j with p'_i >= p_i and p'_j <= p_j such that i loses a seat and j gains one.
-/

/-- A population paradox (Gölz, Peters and Procaccia, Sec. 2, after Robinson and Ullman) of the apportionment solution `f` between `(p, h)` and `(p', h')`: states `i ≠ j` with `p'_i ≥ p_i` and `p'_j ≤ p_j`, yet `i` loses a seat and `j` gains one. -/
def population_paradox {n : ℕ} (f : (Fin n → ℕ) → ℕ → (Fin n → ℕ)) (p p' : Fin n → ℕ) (h h' : ℕ) : Prop :=
  ∃ i j, i ≠ j ∧ p i ≤ p' i ∧ p' j ≤ p j ∧ f p' h' i < f p h i ∧ f p h j < f p' h' j
