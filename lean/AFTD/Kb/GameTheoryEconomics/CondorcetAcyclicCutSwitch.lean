import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover

/-!
# condorcet_acyclic_cut_switch

Topic: social_choice   Node: 9a4a08d72ed9

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

For a finite directed relation, let S and N be vertex sets such that every arrow from S ends in N. For every induced acyclic set A, the set (S minus N) union (A minus the symmetric difference of S and N) is also induced acyclic. No S3 or looplessness hypothesis is needed.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_acyclic_cut_switch
    (m : ℕ) (R : Fin m → Fin m → Prop)
    (S N A : Finset (Fin m))
    (hN : ∀ a b, a ∈ S → R a b → b ∈ N)
    (hA : WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val)) :
    WellFounded (fun a b : {a : Fin m //
      a ∈ (S \ N) ∪ (A \ ((S \ N) ∪ (N \ S)))} => R a.val b.val) := by
  classical
  obtain ⟨σ,hσ⟩ := condorcet_acyclic_cover_ranking_of_wellFounded m
    (fun a b => a ∈ A ∧ R a b)
    (condorcet_acyclic_cover_wellFounded_sources R {a | a ∈ A} hA)
  let rank : Fin m → ℕ := fun a =>
    if a ∈ S then (if a ∈ N then 2*m + (σ a).val else m) else (σ a).val
  refine (measure (fun a : {a : Fin m //
    a ∈ (S \ N) ∪ (A \ ((S \ N) ∪ (N \ S)))} => rank a.val)).wf.mono ?_
  intro a b hab
  have hmem (x : Fin m) (hx : x ∈ (S \ N) ∪ (A \ ((S \ N) ∪ (N \ S)))) :
      (x ∉ S → x ∉ N ∧ x ∈ A) ∧ (x ∈ S → x ∈ N → x ∈ A) := by
    simp only [mem_union,mem_sdiff] at hx
    tauto
  have ha := hmem a.val a.property
  have hb := hmem b.val b.property
  have hσa : a.val ∈ A → (σ a.val).val < (σ b.val).val :=
    fun haA => hσ a.val b.val ⟨haA,hab⟩
  have hσlt := (σ a.val).isLt
  change rank a.val < rank b.val
  by_cases haS : a.val ∈ S
  · have hbN := hN a.val b.val haS hab
    have hbS : b.val ∈ S := by
      by_contra hbS
      exact (hb.1 hbS).1 hbN
    by_cases haN : a.val ∈ N
    · have hlt := hσa (ha.2 haS haN)
      simp only [rank,if_pos haS,if_pos hbS,if_pos haN,if_pos hbN]
      omega
    · simp only [rank,if_pos haS,if_pos hbS,if_neg haN,if_pos hbN]
      omega
  · have hlt := hσa (ha.1 haS).2
    by_cases hbS : b.val ∈ S
    · by_cases hbN : b.val ∈ N <;> simp [rank,haS,hbS,hbN] <;> omega
    · simpa only [rank,if_neg haS,if_neg hbS] using hlt
