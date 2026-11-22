import AFTD.Prelude

/-!
# is_maximal_decreasing_run

Topic: algorithms   Node: ec29ec5b1ea0

Provenance: formalization of a published result. Source: arXiv:2611.26297, Sec. 2

A subsegment S of a list L is a maximal strictly decreasing run if S is a contiguous sublist, S is strictly decreasing, and S cannot be extended to any larger strictly decreasing contiguous sublist of L.
-/

/-- A subsegment is a maximal strictly decreasing run in a list. -/
def is_maximal_decreasing_run {α : Type} [Preorder α] (S L : List α) : Prop :=
  S <:+: L ∧ S.Pairwise (· > ·) ∧ ∀ S', S <:+: S' → S' <:+: L → S'.Pairwise (· > ·) → S' = S
