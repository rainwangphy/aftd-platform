import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgTot

/-!
# agTot_sum

Topic: equilibria   Node: a0733c4b5ebc

The total counts of a pure profile over all strategies sum to the number of players n.
-/

open Finset in
theorem agTot_sum {n s : ℕ} (σ : Fin n → Fin s) : ∑ j, agTot σ j = n := by
  unfold agTot
  rw [← Finset.card_biUnion]
  · have : (Finset.univ.biUnion fun j => Finset.univ.filter (fun q => σ q = j)) = Finset.univ := by
      ext q; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro q _ h1 h2
    exact hij (h1.symm.trans h2)
