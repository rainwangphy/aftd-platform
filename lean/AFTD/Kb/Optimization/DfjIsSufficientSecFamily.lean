import AFTD.Prelude
import AFTD.Kb.Optimization.DfjOneTwoDfjCost
import AFTD.Kb.Optimization.DfjOneTwoTspCost

/-!
# dfjIsSufficientSecFamily

Topic: integer_programming   Node: fcd8ffcab7a1

Provenance: formalization of a published result. Source: arXiv:2611.17386 Definition 1

Given a finite type V, a simple graph H on V, and a finite family 𝒱 of finite subsets of V, 𝒱 is a sufficient subtour elimination family if every S ∈ 𝒱 satisfies 2 ≤ S.card and S.card ≤ Fintype.card V - 2, and the DFJ integer programming cost dfjOneTwoDfjCost H 𝒱 equals the optimal TSP tour cost dfjOneTwoTspCost H.
-/

/-- A family of subtour elimination constraints is sufficient if the DFJ integer programming cost equals the optimal TSP tour cost. -/
def dfjIsSufficientSecFamily {V : Type*} [Fintype V] (H : SimpleGraph V) (𝒱 : Finset (Finset V)) : Prop := (∀ S ∈ 𝒱, 2 ≤ S.card ∧ S.card ≤ Fintype.card V - 2) ∧
  dfjOneTwoDfjCost H 𝒱 = dfjOneTwoTspCost H
