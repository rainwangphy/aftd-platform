import AFTD.Prelude
import AFTD.Kb.Tcs.PrefixReversalGroup
import AFTD.Kb.Tcs.PrefixReversal

/-!
# prefix_reversal_group_le_iff

Topic: combinatorics   Node: f6fdcec5c133

Provenance: helper lemma. Helper for the interior-triple generation question in https://arxiv.org/html/2610.30892v1; classified boundary cases and the primitive-transposition criterion are in https://arxiv.org/html/2511.16959v1, Lemma 1 and Main Theorem.

The generated subgroup is contained in H exactly when all three specified prefix reversals lie in H.
-/

theorem prefix_reversal_group_le_iff (n k m : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) :
    prefix_reversal_group n k m ≤ H ↔
      prefixReversal n k ∈ H ∧ prefixReversal n m ∈ H ∧ prefixReversal n n ∈ H := by
  rw [prefix_reversal_group, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl
