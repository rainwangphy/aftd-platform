import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# nat_sum_lt_of_subset_square_mod_lt

Topic: combinatorics   Node: 00b4b6b7b73e

Provenance: helper lemma. Supporting lemmas for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185. This is the restricted full-box completion route; no claim that an arbitrary long bad sequence contains such a box.

If all summands are below n and every subset sum has residue below n modulo n squared, then their total is below n.
-/

theorem nat_sum_lt_of_subset_square_mod_lt {ι : Type*} [DecidableEq ι]
    (n : ℕ) (hn : 1 < n) (s : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ s, v i < n)
    (hmod : ∀ t ⊆ s, (∑ i ∈ t, v i) % n ^ 2 < n) :
    ∑ i ∈ s, v i < n := by
  induction s using Finset.induction_on with
  | empty => simpa using (show 0 < n by omega)
  | @insert a s ha ih =>
    have hs : ∑ i ∈ s, v i < n := ih
      (fun i hi => hv i (Finset.mem_insert_of_mem hi))
      (fun t ht => hmod t (ht.trans (Finset.subset_insert a s)))
    have ha' : v a < n := hv a (Finset.mem_insert_self a s)
    have hsmall : v a + ∑ i ∈ s, v i < n ^ 2 := by
      have hsq : 0 ≤ (n - 1 : ℤ) ^ 2 := sq_nonneg _
      have hnn : (n : ℤ) ^ 2 ≥ 2 * n - 1 := by nlinarith
      have : (v a : ℤ) + (∑ i ∈ s, v i : ℕ) < (n : ℤ) ^ 2 := by omega
      exact_mod_cast this
    have h := hmod (insert a s) (Finset.Subset.refl _)
    rw [Finset.sum_insert ha, Nat.mod_eq_of_lt hsmall] at h
    simpa only [Finset.sum_insert ha] using h
