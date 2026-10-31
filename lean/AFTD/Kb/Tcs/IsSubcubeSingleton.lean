import AFTD.Prelude
import AFTD.Kb.Tcs.IsSubcube

/-!
# is_subcube_singleton

Topic: combinatorics   Node: f8eae4b04ef7

Provenance: helper lemma. folklore

For any natural number $n$ and any point $c : \mathrm{Fin}\ n \to \mathrm{Bool}$, the singleton subset $\{c\} \subseteq (\mathrm{Fin}\ n \to \mathrm{Bool})$ is a $0$-dimensional subcube `is_subcube 0 {c}`.
-/

/-- Every singleton in the Boolean hypercube is a `0`-dimensional subcube. -/
theorem is_subcube_singleton (n : ℕ) (c : Fin n → Bool) :
    is_subcube 0 ({c} : Finset (Fin n → Bool)) := by
  refine ⟨Finset.univ, c, ?_, ?_⟩
  · simp
  · ext x
    simp [funext_iff]
