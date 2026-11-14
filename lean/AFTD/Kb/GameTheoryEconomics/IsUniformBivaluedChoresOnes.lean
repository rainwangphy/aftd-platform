import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUniformBivaluedChores
import AFTD.Kb.GameTheoryEconomics.SocialWelfareEmpty

/-!
# is_uniform_bivalued_chores_ones

Topic: fair_division   Node: 00f6e92cd661

Provenance: helper lemma. OP-1697

For any number of chores m and any ratio r, the instance where both agents assign cost 1 to every chore is uniform bivalued with ratio r.
-/

/-- The constant cost profile assigning cost 1 to every chore for both agents is uniform bivalued for any ratio r. -/
theorem is_uniform_bivalued_chores_ones (m : ℕ) (r : ℝ) :
  is_uniform_bivalued_chores r (fun (_ : Fin 2) (_ : Fin m) => (1 : ℝ)) := by first | exact social_welfare_empty | (apply social_welfare_empty <;> assumption) | (apply social_welfare_empty <;> simp_all) | simpa using social_welfare_empty | (simp only [is_uniform_bivalued_chores] at *; first | exact social_welfare_empty | (apply social_welfare_empty <;> assumption) | (apply social_welfare_empty <;> simp_all) | simpa using social_welfare_empty)
