import AFTD.Prelude
import AFTD.Kb.Tcs.IsSubcube

/-!
# is_subcube_univ

Topic: combinatorics   Node: ef5aa030b7fc

Provenance: helper lemma. folklore

For any natural number $n$, the entire hypercube $\mathrm{Finset.univ} \subseteq (\mathrm{Fin}\ n \to \mathrm{Bool})$ is an $n$-dimensional subcube `is_subcube n Finset.univ`.
-/

/-- The entire hypercube is an `n`-dimensional subcube of itself. -/
theorem is_subcube_univ (n : ℕ) : is_subcube n (Finset.univ : Finset (Fin n → Bool)) := by
  refine ⟨∅, (fun _ => false : Fin n → Bool), by simp, ?_⟩
  ext x
  simp
