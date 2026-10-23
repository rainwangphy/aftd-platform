import AFTD.Prelude

/-!
# young_diagram_dominates_conjugate

Topic: combinatorics   Node: ea6b6c9efe25

Provenance: formalization of a published result. Source: arXiv:2610.29291 Section 2

A partition $\mu$ dominates its conjugate partition $\mu'$, meaning prefix sums of row lengths are at least prefix sums of column lengths.
-/

/-- A Young diagram dominates its conjugate. -/
def young_diagram_dominates_conjugate (μ : YoungDiagram) : Prop := ∀ k : ℕ, (List.range k).foldl (fun s r => s + μ.rowLen r) 0 ≥
           (List.range k).foldl (fun s c => s + μ.colLen c) 0
