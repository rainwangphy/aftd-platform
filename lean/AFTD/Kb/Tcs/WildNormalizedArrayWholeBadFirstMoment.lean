import AFTD.Prelude
import AFTD.Kb.Tcs.WildNormalizedArraySingleBadCountInvariant
import AFTD.Kb.Tcs.WildProfileConditionedJointCountTransport

/-!
# wild_normalized_array_whole_bad_first_moment

Topic: graphs   Node: 48e5d228dcf0

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

For a symmetric idempotent row-injective array on Fin n and any finite block profile, the sum over all vertex permutations of the number of whole bad colors equals n times the permutation count for any one chosen color. Bad means failure across some nonempty proper block cut; this counts colors, not closed cuts.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

theorem wild_normalized_array_whole_bad_first_moment
    {K : Type*} [Fintype K]
    (n : ℕ) (p : Fin n → K) (A : Fin n → Fin n → Fin n)
    (hAd : ∀ x, A x x = x) (hAs : ∀ x y, A x y = A y x)
    (hAi : ∀ x, Function.Injective (A x)) (a : Fin n) :
    (∑ σ : Equiv.Perm (Fin n),
      (univ.filter fun i : Fin n =>
        wild_profile_bad (wild_profile_permute p σ) (fun x y => A x y = i)).card) =
    n * (univ.filter fun σ : Equiv.Perm (Fin n) =>
      wild_profile_bad (wild_profile_permute p σ) (fun x y => A x y = a)).card := by
  classical
  calc
    _ = ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) =>
        wild_profile_bad (wild_profile_permute p σ) (fun x y => A x y = i)).card := by
      simp_rw [card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ = ∑ _i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) =>
        wild_profile_bad (wild_profile_permute p σ) (fun x y => A x y = a)).card := by
      apply sum_congr rfl
      intro i _
      exact wild_normalized_array_single_bad_count_invariant n p A A
        hAd hAs hAi hAd hAs hAi i a
    _ = _ := by simp
