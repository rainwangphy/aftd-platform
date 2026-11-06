import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramCrossing
import AFTD.Kb.Tcs.DiagramIsConsecutiveAdmissiblePair
import AFTD.Kb.Tcs.DiagramVerticalSlide
import AFTD.Kb.Tcs.DiagramHorizontalSlide

/-!
# DiagramSlidingTree

Topic: combinatorics   Node: e6fcdf13525a

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 4.12

A sliding tree `DiagramSlidingTree D` on a diagram $D$ is either a leaf diagram with no crossings (`∀ u ∈ D, ∀ v ∈ D, ¬ diagram_crossing u v`), or an internal node that chooses a consecutive admissible pair $(b_1, b_2)$ of $D$ and branches into a vertical child sliding tree on `diagram_vertical_slide D b_1 b_2` and a horizontal child sliding tree on `diagram_horizontal_slide D b_1 b_2`.
-/

/-- A sliding tree for a diagram D is a rooted binary tree whose internal nodes choose consecutive admissible pairs and branch by vertical and horizontal slides, with leaves having no crossings. -/
inductive DiagramSlidingTree : Finset (ℕ × ℕ) → Type where | leaf (D : Finset (ℕ × ℕ)) (h : ∀ u ∈ D, ∀ v ∈ D, ¬ diagram_crossing u v) : DiagramSlidingTree D
  | node (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) (hcap : diagram_is_consecutive_admissible_pair D b₁ b₂)
      (left : DiagramSlidingTree (diagram_vertical_slide D b₁ b₂))
      (right : DiagramSlidingTree (diagram_horizontal_slide D b₁ b₂)) : DiagramSlidingTree D
