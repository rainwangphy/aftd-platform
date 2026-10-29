import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUltrametricTransition
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_ultrametric_transition_of_eq_const

Topic: combinatorial_games   Node: 6e7618d11ec9

Provenance: helper lemma. folklore

For a natural number n, a linearly ordered type α, a matrix P : Matrix (Fin n) (Fin n) α, and an element c : α, if all off-diagonal entries of P satisfy P i j = c for all i ≠ j, then P satisfies is_ultrametric_transition P.
-/

/-- Any matrix with constant off-diagonal entries satisfies the ultrametric transition property. -/
theorem is_ultrametric_transition_of_eq_const {n : ℕ} {α : Type*} [LinearOrder α]
    (P : Matrix (Fin n) (Fin n) α) (c : α)
    (hP : ∀ i j, i ≠ j → P i j = c) :
    is_ultrametric_transition P := by
  intro i j k hij hjk hik
  rw [hP i j hij, hP i k hik, hP j k hjk]
  exact le_max_left c c
