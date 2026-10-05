import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGameLipschitz
import AFTD.Kb.GameTheoryEconomics.AgCyc
import AFTD.Kb.GameTheoryEconomics.AgAbsAux
import AFTD.Kb.GameTheoryEconomics.AgMinAux

/-!
# agCyc_lipschitz

Topic: equilibria   Node: 84dc7c8e3081

The cyclic game is 1/8-Lipschitz (for at least two strategies).
-/

open Finset in
/-- The cyclic game is `1/8`-Lipschitz (for at least two strategies). -/
theorem agCyc_lipschitz (n s : ℕ) [NeZero s] (hs : 2 ≤ s) : (agCyc n s).Lipschitz (1 / 8) := by
  intro p i x y hx hy
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
  set D : Fin s → ℚ := fun j => (x j : ℚ) - (y j : ℚ) with hD
  have hsum0 : ∑ j, D j = 0 := by
    simp only [hD, Finset.sum_sub_distrib]
    have hx' : ∑ j, (x j : ℚ) = ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hx
    have hy' : ∑ j, (y j : ℚ) = ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hy
    rw [hx', hy', sub_self]
  -- split the sums at `i` and `i + 1`
  have hmem : i + 1 ∈ (Finset.univ : Finset (Fin s)).erase i := Finset.mem_erase.2 ⟨hi, mem_univ _⟩
  have split : ∀ f : Fin s → ℚ, ∑ j, f j =
      f i + f (i + 1) + ∑ j ∈ ((Finset.univ.erase i).erase (i + 1)), f j := by
    intro f
    rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ hmem]
    ring
  have hrest : ∑ j ∈ ((Finset.univ.erase i).erase (i + 1)), D j = -(D (i + 1) + D i) := by
    have := split D; rw [hsum0] at this; linarith
  have habs : |D (i + 1) + D i| ≤ ∑ j ∈ ((Finset.univ.erase i).erase (i + 1)), |D j| := by
    rw [← abs_neg, ← hrest]; exact Finset.abs_sum_le_sum_abs _ _
  have htot : |D (i + 1)| + |D i| + |D (i + 1) + D i| ≤ ∑ j, |D j| := by
    rw [split (fun j => |D j|)]; linarith
  have key := ag_abs_aux (D (i + 1)) (min (x i : ℚ) 2 - min (y i : ℚ) 2) (D i)
    (ag_min_aux (x i) (y i))
  simp only [agCyc]
  have : ((x (i + 1) : ℚ) + min (x i : ℚ) 2) / 4 - ((y (i + 1) : ℚ) + min (y i : ℚ) 2) / 4
      = (D (i + 1) + (min (x i : ℚ) 2 - min (y i : ℚ) 2)) / 4 := by
    simp only [hD]; ring
  rw [this, abs_div, show |(4 : ℚ)| = 4 by norm_num]
  show _ ≤ 1 / 8 * ∑ j, |D j|
  linarith
