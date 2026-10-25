import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# mms_block_count_valuation

Topic: fair_division   Node: 23dc3e4ac74c

Provenance: helper lemma. step towards mms_threshold_monotone_upper_asymptotic

The valuation induced by a partition: a bundle is worth the number of its blocks that it entirely contains.
-/

def mms_block_count_valuation {m n : ℕ} (P : Fin m → Fin n) : Finset (Fin m) → ℝ := fun S => ((Finset.univ.filter (fun k : Fin n => bundle_of P k ⊆ S)).card : ℝ)
