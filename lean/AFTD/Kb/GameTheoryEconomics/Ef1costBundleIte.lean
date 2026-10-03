import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# ef1cost_bundle_ite

Topic: fair_division   Node: f541729243fa

For two agents, the allocation giving the items of Y to p and the rest to q has bundles Y and its complement.
-/

lemma ef1cost_bundle_ite {m : ℕ} (p q : Fin 2) (hpq : p ≠ q) (Y : Finset (Fin m)) :
    bundle_of (fun j => if j ∈ Y then p else q) p = Y ∧
      bundle_of (fun j => if j ∈ Y then p else q) q = Yᶜ := by
  constructor
  · ext j
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · simp [h]
    · simp [h, Ne.symm hpq]
  · ext j
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    split_ifs with h
    · simp [h, hpq]
    · simp [h]
