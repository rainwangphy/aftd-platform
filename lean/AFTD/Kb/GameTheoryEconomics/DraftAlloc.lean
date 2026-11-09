import AFTD.Prelude

/-!
# draft_alloc

Topic: fair_division   Node: 9c847405801e

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 4.1

Given a preference profile assigning each agent a linear order on objects, a list of agents representing the turn order, and a finite set of remaining objects, draft_alloc recursively computes the allocation assigning each agent a finite set of objects by having the designated picker at each step choose her maximal remaining object.
-/

/-- Sequential draft allocation by recursive greedy choice from remaining objects. -/
def draft_alloc {Agent Object : Type*} [DecidableEq Agent] [DecidableEq Object]
    (succ : Agent → LinearOrder Object) (l : List Agent) (rem : Finset Object) :
    Agent → Finset Object :=
  match l with
  | [] => fun _ => ∅
  | a :: rest =>
    if h : rem.Nonempty then
      let pick := @Finset.max' Object (succ a) rem h
      let rest_alloc := draft_alloc succ rest (rem.erase pick)
      Function.update rest_alloc a (insert pick (rest_alloc a))
    else
      fun _ => ∅
