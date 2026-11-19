import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedLocalCertificate
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedPairs
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedEnds
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedExternal
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedInternal
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# truncation_k4_double_selected_is_strong

Topic: graphs   Node: 4001f9178f96

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The explicit local states form a strong six-edge-coloring of the truncation of the complete four-vertex base.
-/

local instance membership_decidable_strong (v : Fin 4) (e : Fin 6) :
    Decidable (v ∈ truncation_k4_double_selected_ends e) :=
  decidable_of_iff
    (v = (truncation_k4_double_selected_pairs e).1 ∨ v = (truncation_k4_double_selected_pairs e).2)
    Sym2.mem_iff.symm

theorem truncation_k4_double_selected_is_strong :
    truncation_local_states_define_strong_coloring truncation_k4_double_selected_ends
      truncation_k4_double_selected_external truncation_k4_double_selected_internal := by
  have hloop : ∀ e, ¬ (truncation_k4_double_selected_ends e).IsDiag := by decide
  have hcubic : ∀ v, Set.ncard {e | v ∈ truncation_k4_double_selected_ends e} = 3 := by
    intro v
    fin_cases v
    · apply Set.ncard_eq_three.mpr
      refine ⟨0,1,2, by decide, by decide, by decide, ?_⟩
      ext e
      fin_cases e <;> decide
    · apply Set.ncard_eq_three.mpr
      refine ⟨0,3,4, by decide, by decide, by decide, ?_⟩
      ext e
      fin_cases e <;> decide
    · apply Set.ncard_eq_three.mpr
      refine ⟨1,3,5, by decide, by decide, by decide, ?_⟩
      ext e
      fin_cases e <;> decide
    · apply Set.ncard_eq_three.mpr
      refine ⟨2,4,5, by decide, by decide, by decide, ?_⟩
      ext e
      fin_cases e <;> decide
  have hsimple : ∀ e u v z, truncation_k4_double_selected_ends e = s(u,v) →
      z ∈ truncation_exposed_pair truncation_k4_double_selected_ends
        truncation_k4_double_selected_external truncation_k4_double_selected_internal u e →
      z ∈ truncation_exposed_pair truncation_k4_double_selected_ends
        truncation_k4_double_selected_external truncation_k4_double_selected_internal v e → False := by
    simp only [truncation_exposed_pair, Set.mem_setOf_eq]
    decide
  apply (truncation_local_states_strong_coloring_iff (by decide)
    truncation_k4_double_selected_ends hloop hcubic
    truncation_k4_double_selected_external truncation_k4_double_selected_internal
    truncation_k4_double_selected_local_certificate.1
    truncation_k4_double_selected_local_certificate.2.1
    truncation_k4_double_selected_local_certificate.2.2.1).2
  intro e u v he
  refine ⟨(truncation_k4_double_selected_local_certificate.2.2.2.1 e u v he).1, ?_⟩
  rw [Set.disjoint_left]
  exact fun z hz1 hz2 => hsimple e u v z he hz1 hz2
