import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# hunger_firing_state

Topic: combinatorial_games   Node: 524d99deecd3

Provenance: formalization of a published result. Source: arXiv:2610.08949 Section 2

Given a positive natural number n, a linearly ordered type α, and a vector h : Fin n → α, hunger_firing_state h is the smallest index i : Fin n in the standard order on Fin n maximizing h i.
-/

/-- The firing state in a hunger game: the least index among states of maximal hunger. -/
def hunger_firing_state {n : ℕ} [NeZero n] {α : Type*} [LinearOrder α] (h : Fin n → α) : Fin n := ((List.finRange n).argmax h).get (by rw [Option.isSome_iff_ne_none, Ne, List.argmax_eq_none]; intro heq; have hlen : (List.finRange n).length = n := List.length_finRange; rw [heq] at hlen; dsimp at hlen; have : 0 < n := NeZero.pos n; omega)
