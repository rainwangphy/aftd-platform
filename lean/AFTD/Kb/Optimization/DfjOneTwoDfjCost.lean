import AFTD.Prelude

/-!
# dfjOneTwoDfjCost

Topic: integer_programming   Node: a0fedcc3cebf

Provenance: formalization of a published result. Source: arXiv:2611.17386 Section 1

Given a finite type V, a simple graph H on V, and a finite family 𝒱 of finite subsets of V, the DFJ integer programming cost dfjOneTwoDfjCost H 𝒱 is the infimum in ℕ of Fintype.card V plus the number of edges of F not in H, taken over all 2-regular simple graphs F on V such that for every S ∈ 𝒱 there exist vertices u ∈ S and v ∉ S with F.Adj u v.
-/

/-- The optimal DFJ integer programming cost over a family of subtour elimination constraints under the 1,2-metric derived from H. -/
noncomputable def dfjOneTwoDfjCost {V : Type*} [Fintype V] (H : SimpleGraph V) (𝒱 : Finset (Finset V)) : ℕ := open Classical in
  sInf {c | ∃ (F : SimpleGraph V), F.IsRegularOfDegree 2 ∧
    (∀ S ∈ 𝒱, ∃ u ∈ S, ∃ v ∉ S, F.Adj u v) ∧
    Fintype.card V + (F.edgeFinset \ H.edgeFinset).card = c}
