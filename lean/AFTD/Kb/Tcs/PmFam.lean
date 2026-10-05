import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset

/-!
# pmFam

Topic: algorithms   Node: 71930cfd58a1

The poset that is a disjoint union of (at most) two chains: elements of the same colour c are ordered by the rank ρ, elements of different colours are incomparable.
-/

/-- The poset that is a disjoint union of (at most) two chains: elements of the same colour `c` are ordered by the rank `ρ`, elements of different colours are incomparable. -/
def pmFam {n : ℕ} (c : Fin n → Bool) (ρ : Fin n → ℤ) : PMPoset n where
  lt a b := decide (c a = c b ∧ ρ a < ρ b)
  irrefl a := by simp
  trans a b d h1 h2 := by
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
