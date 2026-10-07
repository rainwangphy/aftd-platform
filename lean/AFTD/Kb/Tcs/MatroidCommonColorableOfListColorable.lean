import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_colorable_of_list_colorable

Topic: combinatorics   Node: ba674d3d7d01

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), Sec. 1 (the trivial inequality χ ≤ χ_ℓ)

If (M₁, M₂) is k-list-colorable then it has a common coloring with k colors (take every list to be {0, …, k−1}); hence χ(M₁, M₂) ≤ χ_ℓ(M₁, M₂).
-/

theorem matroid_common_colorable_of_list_colorable {α : Type*} (M₁ M₂ : Matroid α) (k : ℕ)
    (h : matroid_common_list_colorable M₁ M₂ k) : matroid_common_colorable M₁ M₂ k := by
  obtain ⟨c, hc, hind⟩ := h (fun _ => Finset.range k) (fun e _ => by simp)
  exact ⟨c, fun e he => Finset.mem_range.1 (hc e he), hind⟩
