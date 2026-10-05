import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGameNormalized
import AFTD.Kb.GameTheoryEconomics.AgCyc
import AFTD.Kb.GameTheoryEconomics.AgCycV
import AFTD.Kb.GameTheoryEconomics.AgCycUEq

/-!
# agCyc_normalized

Topic: equilibria   Node: 54547e39e3e4

The cyclic game with n = 5 players has payoffs in [0, 1].
-/

open Finset in
/-- The cyclic game with `n = 5` players has payoffs in `[0, 1]`. -/
theorem agCyc_normalized (s : ℕ) [NeZero s] (hs : 2 ≤ s) : (agCyc 5 s).Normalized := by
  intro p i y hy
  have hi : i + 1 ≠ i := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_add] at h'
    have : (1 : Fin s).val = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [this] at h'
    have hi := i.isLt
    rcases Nat.lt_or_ge (i.val + 1) s with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h'; omega
    · have : i.val + 1 = s := by omega
      rw [this, Nat.mod_self] at h'; omega
  have h2 : y (i + 1) + y i ≤ 4 := by
    have := Finset.sum_le_sum_of_subset (f := y) (Finset.subset_univ {i + 1, i})
    rw [Finset.sum_pair hi, hy] at this
    simpa using this
  rw [agCyc_u_eq]
  simp only [agCycV]
  constructor
  · positivity
  · have : y (i + 1) + min (y i) 2 ≤ 4 := by omega
    have : ((y (i + 1) + min (y i) 2 : ℕ) : ℚ) ≤ 4 := by exact_mod_cast this
    linarith
