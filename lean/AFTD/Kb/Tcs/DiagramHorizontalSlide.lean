import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramHorizontalSlideBox

/-!
# diagram_horizontal_slide

Topic: combinatorics   Node: e0ba130c2c02

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.4(2)

The horizontal slide of a diagram $D$ with respect to cells $b_1, b_2$ is the diagram `diagram_horizontal_slide D b_1 b_2` obtained as the image of $D$ under `diagram_horizontal_slide_box D b_1 b_2`.
-/

/-- The diagram obtained by the horizontal slide of an admissible pair. -/
def diagram_horizontal_slide (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) : Finset (ℕ × ℕ) := D.image (diagram_horizontal_slide_box D b₁ b₂)
