import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointFirstBlock
import AFTD.Kb.Tcs.WildJointCanonicalMatching
import AFTD.Kb.Tcs.WildJointBlock

/-!
# wild_joint_alpha_eq_of_matching_isomorphism

Topic: graphs   Node: c02e327e87d8

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry supporting the mixed-moment route for https://arxiv.org/html/2610.22142v1. Exact experiment9566 exposed the missing parity assumption. The original false helper remains retired and its proof record is preserved. No wild-number bound or research advance is claimed.

A permutation preserving the canonical matching and carrying one conditioning set to another preserves its conditional whole-bad probability alpha. This follows by bijecting both the numerator and denominator permutation sets.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000

theorem wild_joint_alpha_eq_of_matching_isomorphism
    (q : ℕ) (S T : Finset (Fin (3*q))) (e : Equiv.Perm (Fin (3*q)))
    (heT : S.image e = T)
    (heR : ∀ x y, wild_joint_canonical_matching q (e x) (e y) ↔
      wild_joint_canonical_matching q x y) :
    wild_joint_alpha q S = wild_joint_alpha q T := by
  classical
  have hblock : ∀ (σ : Equiv.Perm (Fin (3*q))) x,
      wild_joint_block q (σ.trans e) (e x) = wild_joint_block q σ x := by
    intro σ x
    apply Fin.ext
    simp [wild_joint_block]
  have hfirst : ∀ σ : Equiv.Perm (Fin (3*q)),
      wild_joint_first_block q (σ.trans e) = (wild_joint_first_block q σ).image e := by
    intro σ
    ext x
    simp only [wild_joint_first_block,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      exact hx
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
  have hfirstiff : ∀ σ : Equiv.Perm (Fin (3*q)),
      wild_joint_first_block q (σ.trans e) = T ↔ wild_joint_first_block q σ = S := by
    intro σ
    rw [hfirst,← heT]
    exact Finset.image_injective e.injective |>.eq_iff
  have hbad : ∀ σ : Equiv.Perm (Fin (3*q)),
      wild_joint_bad_relation q (wild_joint_block q (σ.trans e)) (wild_joint_canonical_matching q) ↔
      wild_joint_bad_relation q (wild_joint_block q σ) (wild_joint_canonical_matching q) := by
    intro σ
    constructor
    · rintro ⟨B,hB,hBU,hBR⟩
      refine ⟨B,hB,hBU,?_⟩
      intro x y hxy
      have hh := hBR (e x) (e y) ((heR x y).mpr hxy)
      simpa only [hblock] using hh
    · rintro ⟨B,hB,hBU,hBR⟩
      refine ⟨B,hB,hBU,?_⟩
      intro x y hxy
      obtain ⟨x,rfl⟩ := e.surjective x
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [hblock] using hBR x y ((heR x y).mp hxy)
  have hcount (extra : Bool) :
      (univ.filter fun σ : Equiv.Perm (Fin (3*q)) =>
        wild_joint_first_block q σ = S ∧
          (extra = true → wild_joint_bad_relation q (wild_joint_block q σ)
            (wild_joint_canonical_matching q))).card =
      (univ.filter fun σ : Equiv.Perm (Fin (3*q)) =>
        wild_joint_first_block q σ = T ∧
          (extra = true → wild_joint_bad_relation q (wild_joint_block q σ)
            (wild_joint_canonical_matching q))).card := by
    apply card_bij (fun σ _ => σ.trans e)
    · intro σ hσ
      simp only [mem_filter,mem_univ,true_and] at hσ ⊢
      exact ⟨(hfirstiff σ).mpr hσ.1,fun h => (hbad σ).mpr (hσ.2 h)⟩
    · intro σ _ τ _ h
      apply Equiv.ext
      intro x
      have hh := congrArg (fun a : Equiv.Perm (Fin (3*q)) => a x) h
      exact e.injective hh
    · intro τ hτ
      have hc : (τ.trans e.symm).trans e = τ := by ext x; simp
      refine ⟨τ.trans e.symm,?_,hc⟩
      simp only [mem_filter,mem_univ,true_and] at hτ ⊢
      constructor
      · apply (hfirstiff _).mp
        rw [hc]
        exact hτ.1
      · intro h
        apply (hbad _).mp
        rw [hc]
        exact hτ.2 h
  have hnum := hcount true
  have hden := hcount false
  simp only [Bool.false_eq_true, false_implies, and_true, forall_const] at hnum hden
  unfold wild_joint_alpha
  rw [hnum,hden]
