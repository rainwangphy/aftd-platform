import AFTD.Prelude
import AFTD.Kb.NumberTheory.OddSquarefreeIndicator
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# odd_squarefree_indicator_one

Topic: elementary_number_theory   Node: b1a6e4f0e892

Provenance: helper lemma. arXiv:2611.05898, An Asymptotic for E. P. Stein Numbers, Definition 2.1

The odd square-free indicator of $1$ is equal to $1$.
-/

/-- The odd square-free indicator of 1 is 1. -/
theorem odd_squarefree_indicator_one : odd_squarefree_indicator 1 = 1 := by
  unfold odd_squarefree_indicator
  split_ifs with h
  · rfl
  · exfalso
    apply h
    intro p hp hp2 hp_sq
    have : p ^ 2 ≤ 1 := Nat.le_of_dvd Nat.one_pos hp_sq
    have hp_ge : 2 ≤ p := hp.two_le
    nlinarith
