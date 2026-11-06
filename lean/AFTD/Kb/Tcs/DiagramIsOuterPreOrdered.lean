import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramIsPreOrdered

/-!
# diagram_is_outer_pre_ordered

Topic: combinatorics   Node: 8a837ce0c270

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.2 and Lemma 3.12

A cell $u$ in a finite diagram $D$ is outer pre-ordered (`diagram_is_outer_pre_ordered D u`) if it is pre-ordered in $D$ and maximal among pre-ordered cells of $D$ under the componentwise order on $\mathbb{N} \times \mathbb{N}$ (if $v$ is pre-ordered with $u.1 \le v.1$ and $u.2 \le v.2$, then $u = v$).
-/

/-- An outer pre-ordered box is a pre-ordered box that is maximal among pre-ordered boxes under the componentwise order. -/
def diagram_is_outer_pre_ordered (D : Finset (ℕ × ℕ)) (u : ℕ × ℕ) : Prop := diagram_is_pre_ordered D u ∧ ∀ v, diagram_is_pre_ordered D v → u.1 ≤ v.1 → u.2 ≤ v.2 → u = v
