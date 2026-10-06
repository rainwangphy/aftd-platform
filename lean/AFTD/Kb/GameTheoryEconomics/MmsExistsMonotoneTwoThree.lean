import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotoneOfPartitionCover
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotone

/-!
# mms_exists_monotone_two_three

Topic: fair_division   Node: fb0d50568419

Provenance: original. Related work: small case of the threshold μ(n) of arXiv:2610.06125 (On MMS allocations with few items); the paper recalls that two agents and four goods can fail (Table 1)

Two agents with monotone valuations over three goods always have an MMS allocation.
-/

theorem mms_exists_monotone_two_three : mms_exists_monotone 2 3 :=
  mms_exists_monotone_of_partition_cover 2 3 (by norm_num) (by decide)
