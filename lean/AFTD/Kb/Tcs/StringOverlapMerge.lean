import AFTD.Prelude
import AFTD.Kb.Tcs.StringOverlapLen

/-!
# string_overlap_merge

Topic: approximation   Node: 9b3ba5e6e547

Provenance: formalization of a published result. Source: arXiv:2611.16573, Section 2

For two lists x, y : List Γ over an alphabet type Γ with decidable equality, the overlap merge ⟨x,y⟩ is the list consisting of the first x.length − string_overlap_len x y entries of x followed by all of y.
-/

/-- The overlap merge ⟨x, y⟩ = pref(x, y) y. -/
def string_overlap_merge {Γ : Type*} [DecidableEq Γ] (x y : List Γ) : List Γ :=
  x.take (x.length - string_overlap_len x y) ++ y
