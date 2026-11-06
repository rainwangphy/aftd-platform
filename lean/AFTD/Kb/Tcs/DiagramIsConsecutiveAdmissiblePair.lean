import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramIsAdmissiblePair
import AFTD.Kb.Tcs.DiagramIsOuterPreOrdered

/-!
# diagram_is_consecutive_admissible_pair

Topic: combinatorics   Node: 98472a6f2d69

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.3

An admissible pair $(b_1, b_2)$ in a diagram $D$ is consecutive (`diagram_is_consecutive_admissible_pair D b_1 b_2`) if it is admissible and there is no outer pre-ordered cell $b$ of $D$ whose row index lies strictly between that of $b_1$ and $b_2$ ($b_1.1 < b.1 < b_2.1$).
-/

/-- An admissible pair is consecutive if no outer pre-ordered box lies strictly between them in row index. -/
def diagram_is_consecutive_admissible_pair (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) : Prop := diagram_is_admissible_pair D b₁ b₂ ∧ ∀ b, diagram_is_outer_pre_ordered D b → ¬ (b₁.1 < b.1 ∧ b.1 < b₂.1)
