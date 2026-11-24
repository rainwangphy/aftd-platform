import AFTD.Prelude
import AFTD.Kb.Tcs.Op874forestEnds
import AFTD.Kb.Tcs.Op874forestColors
import AFTD.Kb.Tcs.TruncationTwoCommonMissingNoThreeEdges
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_forest_fixed_external_no_strong_completion

Topic: graphs   Node: 52b12c9b6320

Provenance: helper lemma. OP-874: forest fixed-color obstruction, experiments 38417–38419.

The explicit ten-vertex forest fixed-external-color data admit no strong truncation local-state completion.
-/

set_option maxHeartbeats 1000000
private lemma op874fstLoopless : ∀ e, ¬ (op874forest_ends e).IsDiag := by decide
private lemma op874fstCubic : ∀ v : Fin 10,
    Set.ncard {e : Fin 15 | v ∈ op874forest_ends e} = 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  fin_cases v <;> decide
private lemma op874fstProper : ∀ v e f, v ∈ op874forest_ends e → v ∈ op874forest_ends f →
    op874forest_colors e = op874forest_colors f → e=f := by decide

theorem op874_forest_fixed_external_no_strong_completion :
    ¬ ∃ h : Fin 10 → Fin 15 → Fin 6,
      (∀ v e f, v ∈ op874forest_ends e → v ∈ op874forest_ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874forest_ends e → v ∈ op874forest_ends f → h v e ≠ op874forest_colors f) ∧
      truncation_local_states_define_strong_coloring op874forest_ends
        (fun _ e => op874forest_colors e) h := by
  rintro ⟨h, hh, hch, hs⟩
  apply truncation_two_common_missing_no_three_edges
    (by decide : Fintype.card (Fin 6) = 6) op874forest_ends op874fstLoopless op874fstCubic
    (fun _ e => op874forest_colors e) h op874fstProper hh hch hs
    7 3 6 8 7 12 13 1 3
  all_goals decide
