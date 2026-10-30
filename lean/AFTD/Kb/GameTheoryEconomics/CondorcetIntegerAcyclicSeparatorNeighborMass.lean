import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicCutSwitch

/-!
# condorcet_integer_acyclic_separator_neighbor_mass

Topic: social_choice   Node: acd2e2f41e9a

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

If a finite directed relation has a nonnegative integer strict-half separator of its induced acyclic sets, it has such a separator w for which every vertex set S has weight at most the weight of its full outgoing neighborhood. The theorem states only these neighbor-mass inequalities and the preserved strict separation.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_integer_acyclic_separator_neighbor_mass
    (m : ℕ) (R : Fin m → Fin m → Prop) [DecidableRel R]
    (w₀ : Fin m → ℕ)
    (h₀ : ∀ A : Finset (Fin m),
      WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
      2 * (∑ a ∈ A, w₀ a) < ∑ a, w₀ a) :
    ∃ w : Fin m → ℕ,
      (∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a) ∧
      ∀ S : Finset (Fin m),
        (∑ a ∈ S, w a) ≤ ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, R a b), w b := by
  classical
  let P : ℕ → Prop := fun k => ∃ w : Fin m → ℕ,
    (∀ A : Finset (Fin m),
      WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
      2 * (∑ a ∈ A, w a) < ∑ a, w a) ∧ (∑ a, w a) = k
  have hex : ∃ k, P k := ⟨∑ a, w₀ a, w₀, h₀, rfl⟩
  obtain ⟨w,hw,hsum⟩ := Nat.find_spec hex
  refine ⟨w,hw,?_⟩
  intro S
  let N := univ.filter (fun b => ∃ a ∈ S, R a b)
  change (∑ a ∈ S, w a) ≤ ∑ a ∈ N, w a
  by_contra hbad
  have hlt : (∑ a ∈ N, w a) < ∑ a ∈ S, w a := Nat.lt_of_not_ge hbad
  let X := S \ N
  let Y := N \ S
  let v : Fin m → ℕ := fun a => if a ∈ X ∪ Y then 0 else w a
  have hdiff : (∑ a ∈ S, w a) + (∑ a ∈ Y, w a) =
      (∑ a ∈ N, w a) + (∑ a ∈ X, w a) := by
    classical
    rw [← Fintype.sum_ite_mem S w,← Fintype.sum_ite_mem Y w,
      ← Fintype.sum_ite_mem N w,← Fintype.sum_ite_mem X w]
    rw [← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    by_cases haS : a ∈ S <;> by_cases haN : a ∈ N <;>
      simp [X,Y,haS,haN]
  have hXY : (∑ a ∈ Y, w a) < ∑ a ∈ X, w a := by omega
  have hpart : (∑ a, w a) = (∑ a ∈ X, w a) + (∑ a ∈ Y, w a) + ∑ a, v a := by
    rw [← Fintype.sum_ite_mem X w,← Fintype.sum_ite_mem Y w]
    rw [← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    by_cases haS : a ∈ S <;> by_cases haN : a ∈ N <;>
      simp [X,Y,v,haS,haN]
  have hv : ∀ A : Finset (Fin m),
      WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
      2 * (∑ a ∈ A, v a) < ∑ a, v a := by
    intro A hA
    have hT := condorcet_acyclic_cut_switch m R S N A
      (by intro a b ha hab; exact mem_filter.mpr ⟨mem_univ _,a,ha,hab⟩) hA
    have hbound := hw _ hT
    have hvalue : (∑ a ∈ X ∪ (A \ (X ∪ Y)), w a) =
        (∑ a ∈ X, w a) + ∑ a ∈ A, v a := by
      rw [← Fintype.sum_ite_mem (X ∪ (A \ (X ∪ Y))) w,
        ← Fintype.sum_ite_mem X w,← Fintype.sum_ite_mem A v]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro a ha
      by_cases haX : a ∈ X <;> by_cases haY : a ∈ Y <;>
        by_cases haA : a ∈ A <;> simp [v,haX,haY,haA]
    change 2 * (∑ a ∈ X ∪ (A \ (X ∪ Y)), w a) < ∑ a, w a at hbound
    rw [hvalue,hpart] at hbound
    omega
  have hmin : Nat.find hex ≤ ∑ a, v a := Nat.find_min' hex ⟨v,hv,rfl⟩
  omega
