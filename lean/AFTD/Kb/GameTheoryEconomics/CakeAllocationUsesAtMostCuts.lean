import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cake_allocation_uses_at_most_cuts

Topic: fair_division   Node: 0c4266c39f4e

Provenance: formalization of a published result. Source: scout/2610-19733-exact-cut-complexity-of-equal-length-proportional-cake-cutt.md:235

An allocation of the cake [0, 1] among n agents with bundles C : Fin n → Set ℝ uses at most q cuts if there exist an integer k ≤ q and a strictly monotone sequence t : Fin (k + 2) → ℝ with t 0 = 0 and t (Fin.last (k + 1)) = 1 such that for every j : Fin (k + 1), the induced piece (the closed interval Set.Icc (t (Fin.castSucc j)) (t (Fin.succ j)) if j = 0, and the half-open interval Set.Ioc (t (Fin.castSucc j)) (t (Fin.succ j)) if j ≠ 0) is a subset of C i for some agent i : Fin n.
-/

/-- An allocation of the cake among n agents uses at most q cuts if there is a strictly monotone partition with at most q interior cuts whose pieces each lie in some bundle. -/
def cake_allocation_uses_at_most_cuts (n q : ℕ) (C : Fin n → Set ℝ) : Prop :=
  ∃ (k : ℕ) (_hk : k ≤ q) (t : Fin (k + 2) → ℝ),
    StrictMono t ∧
    t 0 = 0 ∧
    t (Fin.last (k + 1)) = 1 ∧
    ∀ j : Fin (k + 1), ∃ i : Fin n,
      (if j = 0 then Set.Icc (t (Fin.castSucc j)) (t (Fin.succ j))
       else Set.Ioc (t (Fin.castSucc j)) (t (Fin.succ j))) ⊆ C i
