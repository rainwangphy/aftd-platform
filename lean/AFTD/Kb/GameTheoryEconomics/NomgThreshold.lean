import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsKNomg
import AFTD.Kb.GameTheoryEconomics.HasObviousGroupManipulation

/-!
# nomg_threshold

Topic: social_choice   Node: 1273f25fe498

Provenance: formalization of a published result. Source: arXiv:2611.26224 Section 5.3 -- Obvious group manipulations in voting

The coalition protection threshold K(f) of a voting rule f on an electorate N is the maximum k ≤ |N| such that f is k-NOMG, that is, no coalition of size at most k has an obvious group manipulation.
-/

/-- The coalition protection threshold K(f) of a voting rule f is the maximum k <= |N| such that f is k-NOMG. -/
noncomputable def nomg_threshold {N A : Type*} [Fintype N] (f : (N → LinearOrder A) → A) : ℕ := by
  classical
  exact Finset.max' ((Finset.range (Fintype.card N + 1)).filter (fun k => is_k_nomg f k))
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), fun C hC hle => by
      have : C.card > 0 := Finset.Nonempty.card_pos hC
      omega⟩⟩
