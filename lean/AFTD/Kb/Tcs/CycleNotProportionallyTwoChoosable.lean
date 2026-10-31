import AFTD.Prelude
import AFTD.Kb.Tcs.CycleNotProportionallyTwoChoosableOfOdd
import AFTD.Kb.Tcs.CycleNotProportionallyTwoChoosableOfEven

/-!
# cycle_not_proportionally_two_choosable

Topic: graphs   Node: 94ce2aa4745c

Provenance: formalization of a published result. Source: scout/2610-33914-improved-bounds-on-proportional-choice-numbers.md:115

For every integer n ≥ 3, the simple n-cycle C_n is not proportionally 2-choosable: it is not the case that for every finite color palette α and every assignment L of 2 colors to each vertex, there exists a proper coloring f of C_n with f(v) ∈ L(v) for all v such that for every color c : α, the number of vertices colored c is either ⌊η_L(c)/2⌋ or ⌈η_L(c)/2⌉, where η_L(c) is the number of vertices whose list contains c.
-/

/-- No simple cycle C_n (n >= 3) is proportionally 2-choosable (arXiv:2610.33914 Theorem 4). -/
theorem cycle_not_proportionally_two_choosable (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (L : Fin n → Finset α),
      (∀ v, (L v).card = 2) →
      ∃ f : (SimpleGraph.cycleGraph n).Coloring α,
        (∀ v, f v ∈ L v) ∧
        ∀ c : α,
          let η := (Finset.univ.filter (fun v => c ∈ L v)).card
          let uses := (Finset.univ.filter (fun v => f v = c)).card
          uses = η / 2 ∨ uses = η ⌈/⌉ 2 := by
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · exact cycle_not_proportionally_two_choosable_of_even n hn hn_even
  · exact cycle_not_proportionally_two_choosable_of_odd n hn hn_odd
