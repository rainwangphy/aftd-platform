import AFTD.Prelude
import AFTD.Kb.Tcs.WildNormalizedArraySingleColorIsomorphism
import AFTD.Kb.Tcs.WildProfileConditionedJointCountTransport

/-!
# wild_normalized_array_single_bad_count_invariant

Topic: graphs   Node: 730f939068a3

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

For any finite block profile p and two symmetric idempotent row-injective arrays on Fin n, the number of vertex permutations for which a chosen whole color fails some nontrivial block cut is identical for any chosen color of either array. No independence or numerical probability bound is asserted.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

theorem wild_normalized_array_single_bad_count_invariant
    {K : Type*} [Fintype K]
    (n : ℕ) (p : Fin n → K) (A B : Fin n → Fin n → Fin n)
    (hAd : ∀ x, A x x = x) (hAs : ∀ x y, A x y = A y x)
    (hAi : ∀ x, Function.Injective (A x))
    (hBd : ∀ x, B x x = x) (hBs : ∀ x y, B x y = B y x)
    (hBi : ∀ x, Function.Injective (B x))
    (a b : Fin n) :
    (univ.filter fun σ : Equiv.Perm (Fin n) =>
      wild_profile_bad (wild_profile_permute p σ) (fun x y => A x y = a)).card =
    (univ.filter fun σ : Equiv.Perm (Fin n) =>
      wild_profile_bad (wild_profile_permute p σ) (fun x y => B x y = b)).card := by
  classical
  obtain ⟨e,_,he⟩ := wild_normalized_array_single_color_isomorphism n A B
    hAd hAs hAi hBd hBs hBi a b
  have hh := wild_profile_joint_bad_count_transport p
    (fun _ : Unit => fun x y => A x y = a)
    (fun _ : Unit => fun x y => B x y = b) ({()} : Finset Unit)
    e (fun _ _ x y => he x y)
  calc
    _ = wild_profile_joint_bad_count p
        (fun _ : Unit => fun x y => A x y = a) ({()} : Finset Unit) := by
      unfold wild_profile_joint_bad_count
      congr 1
      ext σ
      simp
    _ = wild_profile_joint_bad_count p
        (fun _ : Unit => fun x y => B x y = b) ({()} : Finset Unit) := hh
    _ = _ := by
      unfold wild_profile_joint_bad_count
      congr 1
      ext σ
      simp
