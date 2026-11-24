import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAdmissibleLottery

/-!
# has_admissible_lottery

Topic: social_choice   Node: 717202ae023f

Provenance: formalization of a published result. Source: arXiv:2610.24217, Proposition 4.2

For n parties with vote shares p : Fin n → ℝ and house size h, has_admissible_lottery asserts that there exists an admissible lottery dist : Finset (Fin n) → ℝ.
-/

open Classical in
/-- There exists an admissible envy-free lottery for vote shares p at house size h. -/
def has_admissible_lottery {n : ℕ} (p : Fin n → ℝ) (h : ℕ) : Prop :=
  ∃ dist, is_admissible_lottery p h dist
