import AFTD.Prelude
import AFTD.Kb.Tcs.HasCommonSubsequence
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# has_common_subsequence_zero

Topic: information   Node: 5d57b2e0d66f

Provenance: helper lemma. arXiv:2611.21275 Section II-B

Any two vectors of length $n$ have the empty sequence as a common subsequence of length 0.
-/

/-- Any two words have a common subsequence of length 0. -/
lemma has_common_subsequence_zero {n : ℕ} {α : Type*} (u v : Fin n → α) :
    has_common_subsequence u v 0 := by
  refine ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.elim0 a
  · intro a b hab
    exact Fin.elim0 a
  · intro t
    exact Fin.elim0 t
