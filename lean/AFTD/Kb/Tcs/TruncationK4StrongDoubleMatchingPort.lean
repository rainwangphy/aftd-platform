import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedIsStrong
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedExternal
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedInternal
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedEnds
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# truncation_k4_strong_double_matching_port

Topic: graphs   Node: 4070179f701e

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

A strong two-versus-four coloring of the complete four-vertex base can select the matching edge 01 at both endpoints, so exact port selection is an additional constraint.
-/

theorem truncation_k4_strong_double_matching_port :
    truncation_local_states_define_strong_coloring truncation_k4_double_selected_ends
      truncation_k4_double_selected_external truncation_k4_double_selected_internal ∧
    truncation_k4_double_selected_external 0 0 = 0 ∧
    truncation_k4_double_selected_external 2 5 = 1 ∧
    (∀ e : Fin 6, e ≠ 0 → e ≠ 5 → 2 ≤ (truncation_k4_double_selected_external 0 e).val) ∧
    truncation_k4_double_selected_internal 0 0 = 1 ∧
    truncation_k4_double_selected_internal 1 0 = 1 := by
  refine ⟨truncation_k4_double_selected_is_strong, ?_⟩
  decide
