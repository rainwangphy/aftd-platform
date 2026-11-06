import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramIsOuterPreOrdered

/-!
# diagram_is_admissible_pair

Topic: combinatorics   Node: d4192af9b4f5

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.3

A pair of cells $(b_1, b_2)$ is an admissible pair of a diagram $D$ (`diagram_is_admissible_pair D b_1 b_2`) if both $b_1$ and $b_2$ are outer pre-ordered in $D$, $b_1.1 < b_2.1$, and $b_2.2 < b_1.2$ (so $b_2$ lies strictly to the lower-left of $b_1$).
-/

/-- A pair of outer pre-ordered boxes is admissible if the second lies strictly to the lower-left of the first. -/
def diagram_is_admissible_pair (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) : Prop := diagram_is_outer_pre_ordered D b₁ ∧ diagram_is_outer_pre_ordered D b₂ ∧ b₁.1 < b₂.1 ∧ b₂.2 < b₁.2
