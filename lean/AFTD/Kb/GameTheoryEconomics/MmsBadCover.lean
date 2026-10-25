import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# mms_bad_cover

Topic: fair_division   Node: 97589182d408

Provenance: helper lemma. step towards mms_threshold_monotone_upper_asymptotic

A family of n partitions of the m goods into n (nonempty) blocks is a bad cover if no choice of one block per partition gives pairwise disjoint blocks; i.e. there is no allocation sigma with every agent's bundle containing a full block of her own partition.
-/

def mms_bad_cover (n m : ℕ) (P : Fin n → Fin m → Fin n) : Prop := (∀ i, Function.Surjective (P i)) ∧
    ¬ ∃ σ : Fin m → Fin n, ∀ i, ∃ k, bundle_of (P i) k ⊆ bundle_of σ i
