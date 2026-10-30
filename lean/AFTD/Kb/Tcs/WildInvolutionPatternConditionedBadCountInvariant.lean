import AFTD.Prelude
import AFTD.Kb.Tcs.WildInvolutionPartialPatternIsomorphismExtends
import AFTD.Kb.Tcs.WildProfileConditionedJointCountTransport

/-!
# wild_involution_pattern_conditioned_bad_count_invariant

Topic: graphs   Node: 555b6891455e

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

For finite matching patterns with the same internal partner equalities, the permutation counts of a whole-bad matching and any prescribed block assignments to marked pattern vertices agree. Both ambient involutions have a unique fixed point.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem wild_involution_pattern_conditioned_bad_count_invariant
    {V J K : Type*} [Fintype V] [Fintype J] [Fintype K] [DecidableEq V]
    (f g : Equiv.Perm V) (hf : Function.Involutive f) (hg : Function.Involutive g)
    (a b : V) (hfa : ∀ x, f x = x ↔ x = a) (hgb : ∀ x, g x = x ↔ x = b)
    (v w : J → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hpattern : ∀ j k, f (v j) = v k ↔ g (w j) = w k)
    (p : V → K) (M : Finset J) (t : J → K) :
    (univ.filter fun σ : Equiv.Perm V =>
      (∀ j ∈ M, wild_profile_permute p σ (v j) = t j) ∧
      wild_profile_bad (wild_profile_permute p σ) (fun x y => f x = y)).card =
    (univ.filter fun σ : Equiv.Perm V =>
      (∀ j ∈ M, wild_profile_permute p σ (w j) = t j) ∧
      wild_profile_bad (wild_profile_permute p σ) (fun x y => g x = y)).card := by
  classical
  obtain ⟨e,he,hevw⟩ := wild_involution_partial_pattern_isomorphism_extends
    f g hf hg a b hfa hgb v w hv hw hpattern
  have hrel : ∀ x y, g (e x) = e y ↔ f x = y := by
    intro x y
    rw [← he,e.injective.eq_iff]
  have hcondition : ∀ σ : Equiv.Perm V,
      (∀ j ∈ M, wild_profile_permute p (σ.trans e) (w j) = t j) ↔
        ∀ j ∈ M, wild_profile_permute p σ (v j) = t j := by
    intro σ
    simp only [← hevw,wild_profile_permute]
    change (∀ j ∈ M, p (σ.symm (e.symm (e (v j)))) = t j) ↔ _
    simp only [Equiv.symm_apply_apply]
  apply card_bij (fun σ _ => σ.trans e)
  · intro σ hσ
    simp only [mem_filter,mem_univ,true_and] at hσ ⊢
    refine ⟨(hcondition σ).mpr hσ.1,?_⟩
    rw [wild_profile_permute_trans]
    exact (wild_profile_bad_relabel (wild_profile_permute p σ)
      (fun x y => f x = y) (fun x y => g x = y) e hrel).mpr hσ.2
  · intro σ _ τ _ h
    ext x
    exact e.injective (congrArg (fun a : Equiv.Perm V => a x) h)
  · intro τ hτ
    have hcancel : (τ.trans e.symm).trans e = τ := by ext x; simp
    refine ⟨τ.trans e.symm,?_,hcancel⟩
    simp only [mem_filter,mem_univ,true_and] at hτ ⊢
    constructor
    · apply (hcondition (τ.trans e.symm)).mp
      rw [hcancel]
      exact hτ.1
    · apply (wild_profile_bad_relabel (wild_profile_permute p (τ.trans e.symm))
        (fun x y => f x = y) (fun x y => g x = y) e hrel).mp
      rw [← wild_profile_permute_trans,hcancel]
      exact hτ.2
