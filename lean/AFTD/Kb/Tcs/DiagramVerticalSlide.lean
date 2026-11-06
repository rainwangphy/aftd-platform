import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramVerticalSlideBox

/-!
# diagram_vertical_slide

Topic: combinatorics   Node: d55f15494464

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.4(1)

The vertical slide of a diagram $D$ with respect to cells $b_1, b_2$ is the diagram `diagram_vertical_slide D b_1 b_2` obtained as the image of $D$ under `diagram_vertical_slide_box D b_1 b_2`.
-/

/-- The diagram obtained by the vertical slide of an admissible pair. -/
def diagram_vertical_slide (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) : Finset (ℕ × ℕ) := D.image (diagram_vertical_slide_box D b₁ b₂)
