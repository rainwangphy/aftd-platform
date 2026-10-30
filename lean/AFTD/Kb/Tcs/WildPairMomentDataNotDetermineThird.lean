import AFTD.Prelude
import AFTD.Kb.Tcs.WildNineExampleAThird
import AFTD.Kb.Tcs.WildNineExampleBThird
import AFTD.Kb.Tcs.WildNineExampleAPairProfile
import AFTD.Kb.Tcs.WildNineExampleBPairProfile

/-!
# wild_pair_moment_data_not_determine_third

Topic: graphs   Node: d122b38f3aac

Provenance: helper lemma. IN-364 / OP-306, continuation of the finite weighted-partition route for https://arxiv.org/html/2610.22142v1, Sections3.3 and6. Standard permutation-orbit background: Matchings and Representation Theory (2018), Section4.10, https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content. The witness triple system is standard incidence data; these are route helpers or finite method diagnostics. No wild-number bound, new exact sharpness case, general sign theorem, or research advance is claimed.

There is no function of the multiset of pairwise joint bad-color counts and the multiset of unordered triple-witness multiplicities that gives the third falling-factorial bad-color sum for every normalized symmetric idempotent row-injective array on nine vertices. The explicit canonical280 triple partitions are used. This rules out exact reconstruction from these aggregated data; it does not rule out bounds using them, retain labeled pair information, or refute the main wild-number conjecture.
-/

open Finset
open scoped BigOperators
set_option maxRecDepth 12000
set_option maxHeartbeats 6000000
theorem wild_nine_example_a_witness_profile : wild_nine_witness_profile wild_nine_example_a =
    Multiset.replicate 52 0 + Multiset.replicate 28 1 + Multiset.replicate 4 2 := by
  decide +kernel
theorem wild_nine_example_b_witness_profile : wild_nine_witness_profile wild_nine_example_b =
    Multiset.replicate 52 0 + Multiset.replicate 28 1 + Multiset.replicate 4 2 := by
  decide +kernel

theorem wild_pair_moment_data_not_determine_third :
    ¬ ∃ F : Multiset ℕ → Multiset ℕ → ℕ,
      ∀ A : Fin 9 → Fin 9 → Fin 9, wild_nine_first A →
        wild_nine_third_sum A = F (wild_nine_pair_profile A) (wild_nine_witness_profile A) := by
  rintro ⟨F,hF⟩
  have ha := hF wild_nine_example_a wild_nine_example_a_ok
  have hb := hF wild_nine_example_b wild_nine_example_b_ok
  rw [wild_nine_example_a_third,wild_nine_example_a_pair_profile,
    wild_nine_example_a_witness_profile] at ha
  rw [wild_nine_example_b_third,wild_nine_example_b_pair_profile,
    wild_nine_example_b_witness_profile] at hb
  omega
