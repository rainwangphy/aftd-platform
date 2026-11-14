import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OrderPrefix

/-!
# local_no_swap

Topic: general_equilibrium   Node: 14663a789286

Provenance: formalization of a published result. Source: arXiv:2611.16207, Lemma 2

For a cooperative game v on a finite type α and an ordering bijection e : Fin (Fintype.card α) ≃ α, local_no_swap v e states that for all natural numbers k with k + 2 ≤ Fintype.card α, the marginal contribution of player e(k+1) when placed immediately after the prefix of length k is at most its marginal contribution in the original order after the prefix of length k+1: v(insert (e ⟨k+1, _⟩) (order_prefix e k)) - v(order_prefix e k) ≤ v(order_prefix e (k+2)) - v(order_prefix e (k+1)).
-/

/-- The local no-swap condition (1) for an ordering e in a cooperative game v. -/
def local_no_swap {α : Type*} [DecidableEq α] [Fintype α]
    (v : Finset α → ℝ) (e : Fin (Fintype.card α) ≃ α) : Prop := ∀ (k : ℕ) (hk : k + 2 ≤ Fintype.card α),
    v (insert (e ⟨k + 1, by omega⟩) (order_prefix e k)) - v (order_prefix e k) ≤
      v (order_prefix e (k + 2)) - v (order_prefix e (k + 1))
