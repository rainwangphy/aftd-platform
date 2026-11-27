import AFTD.Prelude
import AFTD.Kb.Tcs.Op874AllMaxcutsHamiltonianHaveThreeMonoEdges
import AFTD.Kb.Tcs.SameBitFactorEdgeForcesOuterColorsDistinct
import AFTD.Kb.Tcs.CycleFactorHighColor
import AFTD.Kb.Tcs.CycleMatchingLowColor

/-!
# op874_maxcut_mono_run_forces_three_high_colors

Topic: graphs   Node: 5b4b0c12cf18

Provenance: helper lemma. Maximum-cut palette obstruction for OP-874, using the local compatibility criterion in https://arxiv.org/abs/2610.41950.

Every locally compatible two-versus-four coloring along a maximum matching cut of the displayed fourteen-cycle has a same-bit three-edge factor run using three distinct high colors.
-/

theorem op874_maxcut_mono_run_forces_three_high_colors :
    let pair : Fin 14 → Fin 7 := ![0,1,2,3,4,0,5,2,6,4,1,5,3,6]
    let score : (Fin 7 → Bool) → ℕ := fun t =>
      Finset.univ.sum (fun v : Fin 14 => if t (pair v) ≠ t (pair (v+1)) then 1 else 0)
    ∀ (q : Fin 7 → Bool) (w : Fin 14 → Fin 4) (h : Fin 14 → Fin 3 → Fin 6),
      score q = 10 →
      (∀ j, w (j-1) ≠ w j) →
      (∀ j, Function.Injective (h j)) →
      (∀ j p, h j p ≠ cycle_matching_low_color (q (pair j)) ∧
        h j p ≠ cycle_factor_high_color (w (j-1)) ∧
        h j p ≠ cycle_factor_high_color (w j)) →
      (∀ j, h j 0 ≠ h (j+1) 1 ∧ h j 0 ≠ h (j+1) 2 ∧
        h j 2 ≠ h (j+1) 1 ∧ h j 2 ≠ h (j+1) 2) →
      ∃ i : Fin 14,
        q (pair (i-1)) = q (pair i) ∧
        q (pair i) = q (pair (i+1)) ∧
        q (pair (i+1)) = q (pair (i+2)) ∧
        w (i-1) ≠ w i ∧ w i ≠ w (i+1) ∧ w (i-1) ≠ w (i+1) := by
  intro pair score q w h hscore hproper hinj havoid hstrong
  have hthree : ∀ (t : Fin 7 → Bool), score t = 10 → ∃ i : Fin 14,
      ∀ j : Fin 4, t (pair (i + Fin.ofNat 14 j.val)) = t (pair i) := by
    simpa only [pair, score] using
      (op874_all_maxcuts_hamiltonian_have_three_mono_edges).2.2.2
  obtain ⟨i0, hi0⟩ := hthree q hscore
  have h1fin : i0 + Fin.ofNat 14 (1 : Fin 4).val = i0 + 1 := by rfl
  have h2fin : i0 + Fin.ofNat 14 (2 : Fin 4).val = i0 + 2 := by rfl
  have h3fin : i0 + Fin.ofNat 14 (3 : Fin 4).val = i0 + 3 := by rfl
  have e1 : q (pair i0) = q (pair (i0 + 1)) := by
    rw [← h1fin]
    exact (hi0 1).symm
  have e2 : q (pair (i0 + 1)) = q (pair (i0 + 2)) := by
    rw [← h1fin, ← h2fin]
    exact (hi0 1).trans (hi0 2).symm
  have e3 : q (pair (i0 + 2)) = q (pair (i0 + 3)) := by
    rw [← h2fin, ← h3fin]
    exact (hi0 2).trans (hi0 3).symm
  have hsub1 : (i0 + 1) - 1 = i0 := by ext; simp
  have hadd1 : (i0 + 1) + 1 = i0 + 2 := by ext; simp [Fin.val_add]
  have hadd2 : (i0 + 1) + 2 = i0 + 3 := by ext; simp [Fin.val_add]
  have hbit : q (pair (i0 + 1)) = q (pair ((i0 + 1) + 1)) := by
    rw [hadd1]
    exact e2
  have houter : w ((i0 + 1) - 1) ≠ w ((i0 + 1) + 1) :=
    same_bit_factor_edge_forces_outer_colors_distinct 14 (fun j => q (pair j)) w h
      (i0 + 1) hproper hinj havoid (hstrong (i0 + 1)) hbit
  refine ⟨i0 + 1, ?_, ?_, ?_, ?_, ?_, houter⟩
  · rw [hsub1]
    exact e1
  · rw [hadd1]
    exact e2
  · rw [hadd1, hadd2]
    exact e3
  · exact hproper (i0 + 1)
  · simpa using hproper ((i0 + 1) + 1)
