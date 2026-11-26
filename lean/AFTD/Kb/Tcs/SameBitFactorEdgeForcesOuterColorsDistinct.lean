import AFTD.Prelude
import AFTD.Kb.Tcs.CycleFactorHighColor
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor

/-!
# same_bit_factor_edge_forces_outer_colors_distinct

Topic: graphs   Node: 1e523593a860

Provenance: helper lemma. Local external-palette obstruction for the OP-874 campaign.

Across a same-bit factor edge, the two other incident factor edges must have different high colors in any strong local coloring.
-/

theorem same_bit_factor_edge_forces_outer_colors_distinct
    (n : ℕ) [NeZero n] (b : Fin n → Bool) (edge : Fin n → Fin 4)
    (h : Fin n → Fin 3 → Fin 6) (i : Fin n)
    (hproper : ∀ j, edge (j-1) ≠ edge j)
    (hinj : ∀ j, Function.Injective (h j))
    (havoid : ∀ j p, h j p ≠ cycle_matching_low_color (b j) ∧
      h j p ≠ cycle_factor_high_color (edge (j-1)) ∧
      h j p ≠ cycle_factor_high_color (edge j))
    (hstrong : h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
      h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2)
    (hbit : b i = b (i+1)) : edge (i-1) ≠ edge (i+1) := by
  intro hw
  let low := cycle_matching_low_color (b i)
  let a := cycle_factor_high_color (edge (i-1))
  let z := cycle_factor_high_color (edge i)
  have hla : low ≠ a := by
    intro he
    have eq := congrArg Fin.val he
    dsimp [low,a,cycle_matching_low_color,cycle_factor_high_color] at eq
    split at eq <;> omega
  have hlz : low ≠ z := by
    intro he
    have eq := congrArg Fin.val he
    dsimp [low,z,cycle_matching_low_color,cycle_factor_high_color] at eq
    split at eq <;> omega
  have haz : a ≠ z := by
    intro hz
    apply hproper i
    have hv := congrArg Fin.val hz
    dsimp [a,z,cycle_factor_high_color] at hv
    apply Fin.ext
    omega
  have hx : h i 0 ≠ low ∧ h i 0 ≠ a ∧ h i 0 ≠ z := by
    simpa [low,a,z] using havoid i 0
  have hy : h i 2 ≠ low ∧ h i 2 ≠ a ∧ h i 2 ≠ z := by
    simpa [low,a,z] using havoid i 2
  have hu : h (i+1) 1 ≠ low ∧ h (i+1) 1 ≠ a ∧ h (i+1) 1 ≠ z := by
    have H := havoid (i+1) 1
    simp only [add_sub_cancel_right] at H
    simp only [← hbit, ← hw] at H
    exact ⟨H.1,H.2.2,H.2.1⟩
  have hv : h (i+1) 2 ≠ low ∧ h (i+1) 2 ≠ a ∧ h (i+1) 2 ≠ z := by
    have H := havoid (i+1) 2
    simp only [add_sub_cancel_right] at H
    simp only [← hbit, ← hw] at H
    exact ⟨H.1,H.2.2,H.2.1⟩
  have hxy : h i 0 ≠ h i 2 := by
    intro he
    exact (by decide : (0 : Fin 3) ≠ 2) (hinj i he)
  have huv : h (i+1) 1 ≠ h (i+1) 2 := by
    intro he
    exact (by decide : (1 : Fin 3) ≠ 2) (hinj (i+1) he)
  rcases equal_external_triple_forces_shared_exposed_color low a z
    (h i 0) (h i 2) (h (i+1) 1) (h (i+1) 2)
    hla hlz haz hx hy hu hv hxy huv with h | h | h | h
  · exact hstrong.1 h
  · exact hstrong.2.1 h
  · exact hstrong.2.2.1 h
  · exact hstrong.2.2.2 h
