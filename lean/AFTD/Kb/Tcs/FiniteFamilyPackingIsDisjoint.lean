import AFTD.Prelude

/-!
# finite_family_packing_is_disjoint

Topic: graphs   Node: 74ab814de329

Provenance: helper lemma. Published one-point separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5; finite-family formulation used in the triangle packing campaign.

A subfamily is a packing when its distinct members are disjoint.
-/

def finite_family_packing_is_disjoint {α : Type*} [DecidableEq α] (F P : Finset (Finset α)) : Prop := P ⊆ F ∧ (P : Set (Finset α)).Pairwise Disjoint
