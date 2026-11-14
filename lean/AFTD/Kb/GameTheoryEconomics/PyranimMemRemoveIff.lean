import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimChipSub
import AFTD.Kb.GameTheoryEconomics.PyranimRemove
import AFTD.Kb.GameTheoryEconomics.PlanarNecklaceInjectiveProjection

/-!
# pyranim_mem_remove_iff

Topic: combinatorial_games   Node: c160fe7115f3

Provenance: helper lemma. step towards pyranim_game_iso_iff_graph_iso

A chip x survives the removal of chip c, i.e. x ∈ pyranim_remove X c, if and only if x ∈ X and c is not contained in x: removing a chip deletes exactly the chips that contain it.
-/

/-- Removal is deletion of the principal filter: x survives playing c iff x ∈ X and c is not a subinterval of x. -/
theorem pyranim_mem_remove_iff (X : Finset (ℕ × ℕ)) (c x : ℕ × ℕ) :
    x ∈ pyranim_remove X c ↔ x ∈ X ∧ ¬ pyranim_chip_sub c x := by first | exact planar_necklace_injective_projection | (apply planar_necklace_injective_projection <;> assumption) | (apply planar_necklace_injective_projection <;> simp_all) | simpa using planar_necklace_injective_projection | (simp only [pyranim_remove, pyranim_chip_sub] at *; first | exact planar_necklace_injective_projection | (apply planar_necklace_injective_projection <;> assumption) | (apply planar_necklace_injective_projection <;> simp_all) | simpa using planar_necklace_injective_projection)
