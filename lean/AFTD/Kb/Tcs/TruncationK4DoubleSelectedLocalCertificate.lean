import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedEnds
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedPairs
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedExternal
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedInternal

/-!
# truncation_k4_double_selected_local_certificate

Topic: graphs   Node: b1350a75e7f6

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The explicit four-vertex local states have six distinct local colors, compatible exposed pairs, and select the matching edge 01 at both ends.
-/

local instance membership_decidable_cert (v : Fin 4) (e : Fin 6) :
    Decidable (v ∈ truncation_k4_double_selected_ends e) :=
  decidable_of_iff
    (v = (truncation_k4_double_selected_pairs e).1 ∨ v = (truncation_k4_double_selected_pairs e).2)
    Sym2.mem_iff.symm

theorem truncation_k4_double_selected_local_certificate :
    (∀ v e f, v ∈ truncation_k4_double_selected_ends e →
      v ∈ truncation_k4_double_selected_ends f →
      truncation_k4_double_selected_external v e = truncation_k4_double_selected_external v f → e = f) ∧
    (∀ v e f, v ∈ truncation_k4_double_selected_ends e →
      v ∈ truncation_k4_double_selected_ends f →
      truncation_k4_double_selected_internal v e = truncation_k4_double_selected_internal v f → e = f) ∧
    (∀ v e f, v ∈ truncation_k4_double_selected_ends e →
      v ∈ truncation_k4_double_selected_ends f →
      truncation_k4_double_selected_internal v e ≠ truncation_k4_double_selected_external v f) ∧
    (∀ e u v, truncation_k4_double_selected_ends e = s(u,v) →
      truncation_k4_double_selected_external u e = truncation_k4_double_selected_external v e ∧
      ∀ f g, u ∈ truncation_k4_double_selected_ends f → v ∈ truncation_k4_double_selected_ends g →
        f ≠ e → g ≠ e → truncation_k4_double_selected_internal u f ≠ truncation_k4_double_selected_internal v g) ∧
    truncation_k4_double_selected_internal 0 0 = 1 ∧
    truncation_k4_double_selected_internal 1 0 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
