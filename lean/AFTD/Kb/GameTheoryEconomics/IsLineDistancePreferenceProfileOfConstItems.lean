import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile

/-!
# is_line_distance_preference_profile_of_const_items

Topic: social_choice   Node: 2e0ae2f6254a

Provenance: helper lemma. sanity lemma for is_line_distance_ranking (OP-1158)

Sanity check: when all items sit at one point, every profile of rankings is a distance-ranking profile.
-/

theorem is_line_distance_preference_profile_of_const_items {n : ℕ} (a : Fin n → ℝ) (c : ℝ)
    (pref : Fin n → Equiv.Perm (Fin n)) : is_line_distance_preference_profile a (fun _ => c) pref :=
  fun _ _ _ _ => le_rfl
