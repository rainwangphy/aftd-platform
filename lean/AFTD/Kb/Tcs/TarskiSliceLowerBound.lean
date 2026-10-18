import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tarski_slice_lower_bound

Topic: algorithms   Node: 117d954988ea

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Monotonicity preservation on coordinate slices: fixing coordinate i to any value m ≥ a_i preserves the lower subinterval invariant a_j ≤ f(a^{(i,m)})_j for all coordinates j.
-/

/-- Monotonicity preservation on coordinate slices: increasing coordinate i from a_i to m preserves a ≤ f(a^{(i,m)}). -/
theorem tarski_slice_lower_bound (n k : ℕ) (f : (Fin k → Fin n) → (Fin k → Fin n)) (hf : Monotone f)
    (a : Fin k → Fin n) (ha : a ≤ f a) (i : Fin k) (m : Fin n) (ham : a i ≤ m) (j : Fin k) :
    a j ≤ f (fun l => if l = i then m else a l) j := by
  have hle : a ≤ (fun l => if l = i then m else a l) := by
    intro l
    by_cases h : l = i
    · subst h
      simpa using ham
    · simp [h]
  have hmono := hf hle
  exact le_trans (ha j) (hmono j)
