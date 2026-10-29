import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_ultrametric_transition

Topic: combinatorial_games   Node: 2802177986f4

Provenance: original. Related work: arXiv:2610.08949 (Primitive Periods in Greedy Chip-Firing Games)

For a natural number n and a linearly ordered type α, an n-by-n matrix P : Matrix (Fin n) (Fin n) α satisfies the ultrametric transition property if for every triple of pairwise distinct indices i, j, k : Fin n (satisfying i ≠ j, j ≠ k, and i ≠ k), P i j ≤ max (P i k) (P j k).
-/

/-- Predicate that a transition matrix satisfies the ultrametric inequality on all pairwise distinct triples of states in Fin n. -/
def is_ultrametric_transition {n : ℕ} {α : Type*} [LinearOrder α]
    (P : Matrix (Fin n) (Fin n) α) : Prop := ∀ (i j k : Fin n), i ≠ j → j ≠ k → i ≠ k → P i j ≤ max (P i k) (P j k)
