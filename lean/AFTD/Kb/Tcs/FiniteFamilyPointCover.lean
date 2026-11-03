import AFTD.Prelude

/-!
# finite_family_point_cover

Topic: graphs   Node: 62184fc394dd

Provenance: helper lemma. Published one-point separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5; finite-family formulation used in the triangle packing campaign.

A set of points meets every member of a finite family.
-/

def finite_family_point_cover {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α) : Prop := ∀ A ∈ F, ¬ Disjoint A C
