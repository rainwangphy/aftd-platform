import AFTD.Prelude
import AFTD.Kb.Tcs.WildNineExampleAThird

/-!
# wild_nine_example_b_pair_profile

Topic: graphs   Node: b14a30d875c9

Provenance: helper lemma. IN-364 / OP-306, continuation of the finite weighted-partition route for https://arxiv.org/html/2610.22142v1, Sections3.3 and6. Standard permutation-orbit background: Matchings and Representation Theory (2018), Section4.10, https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content. The witness triple system is standard incidence data; these are route helpers or finite method diagnostics. No wild-number bound, new exact sharpness case, general sign theorem, or research advance is claimed.

For the explicit normalized nine-vertex array B, the multiset of pairwise joint bad-color counts is 32 copies of4 and4 copies of13. Here D counts colors closing at least one of the three triple blocks; the arrays and finite partition family are explicit computable definitions. This is a certificate for a method diagnostic, not a wild-number claim.
-/

open Finset
open scoped BigOperators
set_option maxRecDepth 12000
set_option maxHeartbeats 6000000

theorem wild_nine_example_b_pair_profile : wild_nine_pair_profile wild_nine_example_b =
    Multiset.replicate 32 4 + Multiset.replicate 4 13 := by
  decide +kernel
