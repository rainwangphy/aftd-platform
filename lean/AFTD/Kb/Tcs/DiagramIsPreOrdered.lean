import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramCrossing

/-!
# diagram_is_pre_ordered

Topic: combinatorics   Node: b1cbe1351a4f

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.2

A cell $u$ in a finite diagram $D$ is pre-ordered (`diagram_is_pre_ordered D u`) if $u \in D$ and there exists a cell $v \in D$ such that $u$ and $v$ form a crossing (`diagram_crossing u v`).
-/

/-- A box in a diagram is pre-ordered if it belongs to some crossing of the diagram. -/
def diagram_is_pre_ordered (D : Finset (ℕ × ℕ)) (u : ℕ × ℕ) : Prop := u ∈ D ∧ ∃ v ∈ D, diagram_crossing u v
