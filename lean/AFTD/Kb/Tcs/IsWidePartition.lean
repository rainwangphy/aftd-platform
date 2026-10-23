import AFTD.Prelude
import AFTD.Kb.Tcs.YoungDiagramDominatesConjugate

/-!
# is_wide_partition

Topic: combinatorics   Node: d39b931a82f1

Provenance: formalization of a published result. Source: arXiv:2610.29291 Definition 2.2

A Young diagram $d$ is wide if for every Young diagram $\mu$ whose list of row lengths $\mu.\text{rowLens}$ is a sublist of $d.\text{rowLens}$ (obtained by deleting rows of $d$), $\mu$ dominates its conjugate diagram.
-/

/-- A Young diagram is wide if every subpartition obtained by deleting rows dominates its conjugate. -/
def is_wide_partition (d : YoungDiagram) : Prop := ∀ μ : YoungDiagram, μ.rowLens.Sublist d.rowLens → young_diagram_dominates_conjugate μ
