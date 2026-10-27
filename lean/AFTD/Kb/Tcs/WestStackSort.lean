import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# west_stack_sort

Topic: combinatorics   Node: 48540156f0e8

Provenance: formalization of a published result. Source: arXiv:2610.32824 Section 1

West's stack-sorting map s acts on a list by maintaining an auxiliary stack, popping elements strictly smaller than the next input element to the output before pushing, and popping the remaining stack once the input is exhausted.
-/

/-- West's stack-sorting operator on lists of linearly ordered elements. -/
def west_stack_sort {α : Type*} [LinearOrder α] (l : List α) : List α := aux l []
where
  aux : List α → List α → List α
    | [], stack => stack
    | x :: xs, [] => aux xs [x]
    | x :: xs, s :: stack =>
      if s < x then
        s :: aux (x :: xs) stack
      else
        aux xs (x :: s :: stack)
  termination_by xs stack => (xs.length, stack.length)
