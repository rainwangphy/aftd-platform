import AFTD.Prelude

/-!
# diagram_crossing

Topic: combinatorics   Node: d0ddd240db01

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.2

Two cells $u, v \in \mathbb{N} \times \mathbb{N}$ form a crossing (`diagram_crossing u v`) if $(u.1 < v.1 \land v.2 < u.2) \lor (v.1 < u.1 \land u.2 < v.2)$.
-/

/-- Two cells in ℕ × ℕ cross if one lies strictly south-west of the other. -/
def diagram_crossing (u v : ℕ × ℕ) : Prop := (u.1 < v.1 ∧ v.2 < u.2) ∨ (v.1 < u.1 ∧ u.2 < v.2)
