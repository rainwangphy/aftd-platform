import AFTD.Prelude

/-!
# Matroid.IsCyclic

Topic: graphs   Node: 421629b35936

Provenance: formalization of a published result. Source: arXiv:2611.15741 Definition 2.9

A subset X of the ground set of a matroid M is cyclic if it is a union of circuits of M.
-/

/-- A subset of the ground set of a matroid is cyclic if it is a union of circuits. -/
def Matroid.IsCyclic {α : Type*} (M : Matroid α) (X : Set α) : Prop := ∃ 𝒮 : Set (Set α), (∀ C ∈ 𝒮, M.IsCircuit C) ∧ X = ⋃₀ 𝒮
