import AFTD.Prelude
import AFTD.Kb.Tcs.IsValidTimelyPacking
import AFTD.Kb.Tcs.TimelyBin
import AFTD.Kb.Tcs.TimelyItem

/-!
# optimal_timely_bin_count

Topic: online_algorithms   Node: 26fdb443ec5b

Provenance: formalization of a published result. Source: arXiv:2611.09611, Section 1.1

The optimal offline number of bins `optimal_timely_bin_count I` for an instance `I : Finset TimelyItem` is the infimum in `ℕ` of the cardinality of `P` over all finite sets of bins `P : Finset TimelyBin` that form a valid timely packing of `I`.
-/

/-- The optimal offline number of bins for an instance I is the minimum cardinality of a valid packing. -/
noncomputable def optimal_timely_bin_count (I : Finset TimelyItem) : ℕ :=
  sInf {n : ℕ | ∃ P : Finset TimelyBin, is_valid_timely_packing I P ∧ P.card = n}
