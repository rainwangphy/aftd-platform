import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramCrossing
import AFTD.Kb.Tcs.DiagramSlidingTree
import AFTD.Kb.Tcs.DiagramSlideExpansionAgreesWithDescents
import AFTD.Kb.Tcs.OpenProblem1285PartialNoCrossings

/-!
# open_problem_1285_exists_tree_of_no_crossings

Topic: combinatorics   Node: ec72400d7eb9

Provenance: helper lemma. arXiv:2611.07715, Theorem 3.22

For every finite diagram $D \subseteq \mathbb{N} \times \mathbb{N}$ having no crossings (`∀ u ∈ D, ∀ v ∈ D, ¬ diagram_crossing u v`), there exists a sliding tree `t : DiagramSlidingTree D` such that `diagram_slide_expansion_agrees_with_descents D t` holds.
-/

/-- For any diagram D with no crossings, there exists a sliding tree satisfying agreement with descents. -/
theorem open_problem_1285_exists_tree_of_no_crossings (D : Finset (ℕ × ℕ)) (h : ∀ u ∈ D, ∀ v ∈ D, ¬ diagram_crossing u v) : ∃ t : DiagramSlidingTree D, diagram_slide_expansion_agrees_with_descents D t := by
  exact ⟨DiagramSlidingTree.leaf D h, open_problem_1285_partial_no_crossings D h⟩
