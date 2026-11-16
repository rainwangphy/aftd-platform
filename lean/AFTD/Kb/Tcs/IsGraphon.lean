import AFTD.Prelude
import AFTD.Kb.Tcs.IsDigraphon

/-!
# is_graphon

Topic: graphs   Node: ce64ee0c9ca9

Provenance: formalization of a published result. Source: arXiv:2611.17885 Section 1

A function W : ℝ → ℝ → ℝ is a graphon if it is a digraphon and is symmetric, meaning W x y = W y x for all x, y.
-/

/-- A graphon is a symmetric measurable [0, 1]-valued function on the unit square. -/
def is_graphon (W : ℝ → ℝ → ℝ) : Prop := is_digraphon W ∧ (∀ x y, W x y = W y x)
