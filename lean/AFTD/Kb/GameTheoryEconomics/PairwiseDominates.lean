import AFTD.Prelude

/-!
# pairwise_dominates

Topic: fair_division   Node: 9d9fe43e008c

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 2.2

A finite bundle S : Finset α pairwise-dominates a finite bundle S' : Finset α for an agent with weak preference relation le : α → α → Prop if there is an injection f : α → α mapping each element y of S' into S such that le y (f y) holds.
-/

/-- Pairwise dominance of finite bundle S over finite bundle S' under item preference relation le. -/
def pairwise_dominates {α : Type*} (le : α → α → Prop) (S S' : Finset α) : Prop := ∃ (f : α → α), (∀ y ∈ S', f y ∈ S) ∧ (∀ y₁ ∈ S', ∀ y₂ ∈ S', f y₁ = f y₂ → y₁ = y₂) ∧ ∀ y ∈ S', le y (f y)
