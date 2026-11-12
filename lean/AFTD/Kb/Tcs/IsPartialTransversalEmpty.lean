import AFTD.Prelude
import AFTD.Kb.Tcs.IsPartialTransversal
import AFTD.Kb.Tcs.In715DeficitPrivateTip

/-!
# is_partial_transversal_empty

Topic: combinatorics   Node: 834e2e4a8ab2

Provenance: helper lemma. folklore

For any dimension δ : ℕ and any finset of cells S in Fin δ × Fin δ, the empty finset ∅ is a partial transversal of S (is_partial_transversal S ∅).
-/

/-- The empty set is a partial transversal of any set of cells. -/
theorem is_partial_transversal_empty {δ : ℕ} (S : Finset (Fin δ × Fin δ)) : is_partial_transversal S ∅ := by first | exact in715_deficit_private_tip | (apply in715_deficit_private_tip <;> assumption) | (apply in715_deficit_private_tip <;> simp_all) | simpa using in715_deficit_private_tip | (simp only [is_partial_transversal] at *; first | exact in715_deficit_private_tip | (apply in715_deficit_private_tip <;> assumption) | (apply in715_deficit_private_tip <;> simp_all) | simpa using in715_deficit_private_tip)
