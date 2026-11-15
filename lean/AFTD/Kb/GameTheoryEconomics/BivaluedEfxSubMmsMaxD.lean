import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasBivaluedEfxSubMmsInstance

/-!
# bivalued_efx_sub_mms_max_d

Topic: fair_division   Node: 82a8f0bd04d4

Provenance: original. Related work: arXiv:2611.15582

For natural numbers n and R, the supremum of the set of natural numbers d such that has_bivalued_efx_sub_mms_instance n R d holds.
-/

/-- The largest integer d for which some n-agent additive instance with item values in {1, R} has a complete EFX allocation leaving an agent strictly below her 1-out-of-d maximin share. -/
noncomputable def bivalued_efx_sub_mms_max_d (n : ℕ) (R : ℕ) : ℕ :=
  sSup {d : ℕ | has_bivalued_efx_sub_mms_instance n R d}
