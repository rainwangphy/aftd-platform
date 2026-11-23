import AFTD.Prelude
import AFTD.Kb.Tcs.CableSteinerOpt
import AFTD.Kb.Tcs.RatSegmentsUnion

/-!
# cable_steiner_opt_singleton

Topic: approximation   Node: 8cab9bf03fd5

Provenance: helper lemma. Sanity check of cable_steiner_opt: one connected cable needs no added segments.

For a single cable c whose union is connected, the cable Steiner optimum of [c] is 0.
-/

theorem cable_steiner_opt_singleton (c : List ((ℚ × ℚ) × (ℚ × ℚ)))
    (hc : IsConnected (rat_segments_union c)) : cable_steiner_opt [c] = 0 := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro L ⟨T, -, rfl⟩
      exact Finset.sum_nonneg fun t _ => dist_nonneg
    · refine ⟨∅, ?_, by simp⟩
      simpa using hc
  · apply le_csInf
    · exact ⟨0, ∅, by simpa using hc, by simp⟩
    · rintro L ⟨T, -, rfl⟩
      exact Finset.sum_nonneg fun t _ => dist_nonneg
