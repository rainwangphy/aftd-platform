import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramCrossing
import AFTD.Kb.Tcs.DiagramSlidingTree
import AFTD.Kb.Tcs.DiagramSlideExpansionAgreesWithDescents
import AFTD.Kb.Tcs.TerminalBoxes
import AFTD.Kb.Tcs.IsStandardYoungTableauList
import AFTD.Kb.Tcs.ListDescentAt

/-!
# open_problem_1285_partial_no_crossings

Topic: combinatorics   Node: 8a9313bcb9b4

Provenance: helper lemma. arXiv:2611.07715, Theorem 3.22

For every finite diagram $D \subseteq \mathbb{N} \times \mathbb{N}$ having no crossings (`∀ u ∈ D, ∀ v ∈ D, ¬ diagram_crossing u v`), the leaf sliding tree `DiagramSlidingTree.leaf D h` satisfies agreement with descents (`diagram_slide_expansion_agrees_with_descents D (DiagramSlidingTree.leaf D h)`).
-/

/-- For any diagram D with no crossings, the leaf sliding tree satisfies agreement with descents. -/
theorem open_problem_1285_partial_no_crossings (D : Finset (ℕ × ℕ)) (h : ∀ u ∈ D, ∀ v ∈ D, ¬ diagram_crossing u v) : diagram_slide_expansion_agrees_with_descents D (DiagramSlidingTree.leaf D h) := by
  intro l _ k
  rfl
