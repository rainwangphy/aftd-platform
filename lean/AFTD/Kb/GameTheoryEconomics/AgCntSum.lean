import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCnt

/-!
# agCnt_sum

Topic: equilibria   Node: a04211345e8a

The counts of the others always form a partition of n − 1.
-/

open Finset in
/-- The counts of the others always form a partition of `n − 1`. -/
theorem agCnt_sum {n s : ℕ} (σ : Fin n → Fin s) (p : Fin n) :
    ∑ j, agCnt σ p j = n - 1 := by
  unfold agCnt
  rw [← Finset.card_biUnion]
  · have : (Finset.univ.biUnion fun j => Finset.univ.filter (fun q => q ≠ p ∧ σ q = j)) = Finset.univ.erase p := by
      ext q; simp [and_comm]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro q _ h1 h2
    exact hij (h1.2.symm.trans h2.2)
