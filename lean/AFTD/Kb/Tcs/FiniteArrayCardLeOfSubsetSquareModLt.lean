import AFTD.Prelude
import AFTD.Kb.Tcs.NatSumLtOfSubsetSquareModLt

/-!
# finite_array_card_le_of_subset_square_mod_lt

Topic: combinatorics   Node: 7485fb7f7029

Provenance: helper lemma. Supporting lemmas for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185. This is the restricted full-box completion route; no claim that an arbitrary long bad sequence contains such a box.

A nonzero nonnegative array whose entries and all coordinate subset-sum residues modulo n squared are below n has at most r(n-1) rows.
-/

theorem finite_array_card_le_of_subset_square_mod_lt {ι : Type*}
    [Fintype ι] [DecidableEq ι] (n r : ℕ) (hn : 1 < n)
    (v : ι → Fin r → ℕ)
    (hv : ∀ i j, v i j < n)
    (hpos : ∀ i, 0 < ∑ j, v i j)
    (hmod : ∀ s : Finset ι, ∀ j, (∑ i ∈ s, v i j) % n ^ 2 < n) :
    Fintype.card ι ≤ r * (n - 1) := by
  have hsum : ∀ j, ∑ i, v i j ≤ n - 1 := by
    intro j
    have h := nat_sum_lt_of_subset_square_mod_lt n hn Finset.univ (fun i => v i j)
      (fun i _ => hv i j) (fun s _ => hmod s j)
    omega
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, ∑ j, v i j := Finset.sum_le_sum (fun i _ => hpos i)
    _ = ∑ j, ∑ i, v i j := Finset.sum_comm
    _ ≤ ∑ _j : Fin r, (n - 1) := Finset.sum_le_sum (fun j _ => hsum j)
    _ = r * (n - 1) := by simp
