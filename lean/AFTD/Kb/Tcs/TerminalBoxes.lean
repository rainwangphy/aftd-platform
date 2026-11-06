import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramSlidingTree
import AFTD.Kb.Tcs.DiagramVerticalSlideBox
import AFTD.Kb.Tcs.DiagramHorizontalSlideBox
import AFTD.Kb.Tcs.DiagramIsConsecutiveAdmissiblePair
import AFTD.Kb.Tcs.DiagramVerticalSlide
import AFTD.Kb.Tcs.DiagramCrossing
import AFTD.Kb.Tcs.DiagramHorizontalSlide

/-!
# terminal_boxes

Topic: combinatorics   Node: 9f8cbfd852e3

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 4.12 and Proposition 3.21

Given a sliding tree `t : DiagramSlidingTree D` and a list $l$ of boxes representing a tableau on $D$, `terminal_boxes t l` transports $l$ to the leaf: at each node with consecutive admissible pair $(b_1, b_2)$, if $b_2$ precedes $b_1$ in $l$ ($l.idxOf b_2 < l.idxOf b_1$, corresponding to the entry of $b_1$ being strictly greater than the entry of $b_2$), it slides vertically and continues in the left subtree; otherwise it slides horizontally and continues in the right subtree.
-/

/-- Transports an ordered list of boxes along the root-to-leaf path determined by entry comparison at each node. -/
def terminal_boxes {D : Finset (ℕ × ℕ)} (t : DiagramSlidingTree D) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := match t with
  | DiagramSlidingTree.leaf _ _ => l
  | DiagramSlidingTree.node D b₁ b₂ _ left right =>
    if l.idxOf b₂ < l.idxOf b₁ then
      terminal_boxes left (l.map (diagram_vertical_slide_box D b₁ b₂))
    else
      terminal_boxes right (l.map (diagram_horizontal_slide_box D b₁ b₂))
