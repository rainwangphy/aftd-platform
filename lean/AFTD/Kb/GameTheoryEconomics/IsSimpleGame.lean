import AFTD.Prelude

/-!
# is_simple_game

Topic: general_equilibrium   Node: 200d23d5417d

A simple game on n players is a monotone function v from coalitions to {0,1} with v(empty) = 0 and v(all players) = 1; the coalitions with value 1 are winning.
-/

/-- A simple game on `n` players (Fried, arXiv:2607.07013, Sec. 10): a monotone `v : 2^[n] → {0,1}` with `v(∅) = 0` and `v([n]) = 1`; coalitions with `v S = true` are winning. -/
def is_simple_game {n : ℕ} (v : Finset (Fin n) → Bool) : Prop :=
  (∀ S T, S ⊆ T → v S = true → v T = true) ∧ v ∅ = false ∧ v Finset.univ = true
