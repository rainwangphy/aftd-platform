import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# tarski_slice_upper_bound

Topic: algorithms   Node: 9a68a1bbb020

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Monotonicity preservation on coordinate slices (upper bound): fixing coordinate i to any value m ≤ b_i preserves the upper subinterval invariant f(b^{(i,m)})_j ≤ b_j for all coordinates j.
-/

/-- Monotonicity preservation on coordinate slices: decreasing coordinate i from b_i to m preserves f(b^{(i,m)}) ≤ b. -/
theorem tarski_slice_upper_bound (n k : ℕ) (f : (Fin k → Fin n) → (Fin k → Fin n)) (hf : Monotone f)
    (b : Fin k → Fin n) (hb : f b ≤ b) (i : Fin k) (m : Fin n) (hbm : m ≤ b i) (j : Fin k) :
    f (fun l => if l = i then m else b l) j ≤ b j := by
  have h_le : (fun l => if l = i then m else b l) ≤ b := by
    intro l
    dsimp
    split_ifs with h
    · subst h
      exact hbm
    · exact le_rfl
  exact (hf h_le j).trans (hb j)
