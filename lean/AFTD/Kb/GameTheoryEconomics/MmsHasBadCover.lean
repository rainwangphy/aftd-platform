import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsBadCover

/-!
# mms_has_bad_cover

Topic: fair_division   Node: d9695179ea13

Provenance: helper lemma. step towards mms_threshold_monotone_upper_asymptotic

There exist n partitions of the m goods into n nonempty blocks with no covering allocation.
-/

def mms_has_bad_cover (n m : ℕ) : Prop := ∃ P : Fin n → Fin m → Fin n, mms_bad_cover n m P
