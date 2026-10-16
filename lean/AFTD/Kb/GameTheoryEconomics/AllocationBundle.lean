import AFTD.Prelude

/-!
# allocation_bundle

Topic: fair_division   Node: b029307a4615

Provenance: formalization of a published result. Source: arXiv:2610.14994 (Best-of-both-worlds fair division via subsidies), Sec. 2 (allocations of indivisible goods).

For a complete allocation A of the goods M to the agents N (each good to one agent), the bundle of agent i is the set of goods A assigns to i.
-/

/-- The bundle `A_i` of agent `i` in the complete allocation `A : M → N`. -/
def allocation_bundle {N M : Type*} [Fintype M] [DecidableEq N] (A : M → N) (i : N) : Finset M :=
  Finset.univ.filter fun g => A g = i
