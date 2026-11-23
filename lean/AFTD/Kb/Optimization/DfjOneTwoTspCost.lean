import AFTD.Prelude

/-!
# dfjOneTwoTspCost

Topic: integer_programming   Node: 56ee93d4822d

Provenance: formalization of a published result. Source: arXiv:2611.17386 Section 1

Given a finite type V and a simple graph H on V, the optimal 1,2-TSP tour cost dfjOneTwoTspCost H is the infimum in ℕ of Fintype.card V plus the number of edges of C not in H, taken over all connected 2-regular simple graphs C on V.
-/

/-- The optimal TSP tour cost in ℕ under the 1,2-metric derived from a base graph H. -/
noncomputable def dfjOneTwoTspCost {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ := open Classical in
  sInf {c | ∃ (C : SimpleGraph V), C.IsRegularOfDegree 2 ∧ C.Connected ∧ Fintype.card V + (C.edgeFinset \ H.edgeFinset).card = c}
