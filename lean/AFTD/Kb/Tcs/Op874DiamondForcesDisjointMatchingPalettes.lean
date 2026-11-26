import AFTD.Prelude
import AFTD.Kb.Tcs.SameBitFactorEdgeForcesOuterColorsDistinct
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.CycleFactorHighColor

/-!
# op874_diamond_forces_disjoint_matching_palettes

Topic: graphs   Node: d5a5c0dd136c

Provenance: helper lemma. Forced mixture of matching-palette intersection types for OP-874; https://arxiv.org/abs/2610.41950.

On a four-cycle whose vertex 0 shares its low color with vertices 1 and 3, compatible local states force all four factor-edge colors to differ. Thus the high palettes at opposite vertices 1 and 3 are disjoint, including when those vertices are joined by a matching edge.
-/

theorem op874_diamond_forces_disjoint_matching_palettes
    (b : Fin 4 → Bool) (edge : Fin 4 → Fin 4) (h : Fin 4 → Fin 3 → Fin 6)
    (hproper : ∀ j, edge (j-1) ≠ edge j)
    (hinj : ∀ j, Function.Injective (h j))
    (havoid : ∀ j p, h j p ≠ cycle_matching_low_color (b j) ∧
      h j p ≠ cycle_factor_high_color (edge (j-1)) ∧
      h j p ≠ cycle_factor_high_color (edge j))
    (hstrong : ∀ i, h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
      h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2)
    (hbit01 : b 0 = b 1) (hbit03 : b 0 = b 3) :
    Disjoint ({edge 0,edge 1} : Finset (Fin 4)) {edge 2,edge 3} := by
  have h31 : edge 3 ≠ edge 1 :=
    same_bit_factor_edge_forces_outer_colors_distinct 4 b edge h 0 hproper hinj havoid (hstrong 0) hbit01
  have h20 : edge 2 ≠ edge 0 :=
    same_bit_factor_edge_forces_outer_colors_distinct 4 b edge h 3 hproper hinj havoid (hstrong 3) hbit03.symm
  have h30 : edge 3 ≠ edge 0 := hproper 0
  have h12 : edge 1 ≠ edge 2 := hproper 2
  simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨⟨h20.symm, h30.symm⟩, ⟨h12, h31.symm⟩⟩
