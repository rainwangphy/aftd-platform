import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFiniteStrictSeparatorIntegerWeights
import AFTD.Kb.GameTheoryEconomics.CondorcetIntegerAcyclicSeparatorNeighborMass
import AFTD.Kb.GameTheoryEconomics.CondorcetIntegerNeighborMassClonePermutation
import AFTD.Kb.GameTheoryEconomics.CondorcetPermutationNegativeClosedWalk

/-!
# condorcet_strict_half_separator_acyclic_cover_closed_walk

Topic: social_choice   Node: 54bc54775332

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. Supporting reduction from the proved strict-half circulation bridge. Scratch ClosedWalk.lean passed trusted-axiom checking. Standard finite matching and orbit averaging; no research novelty or new election bound is claimed.

If a finite relation has a nonnegative real strict-half acyclic separator, then every positive finite family of induced acyclic sets admits a nonempty closed directed walk whose total membership count in the family, doubled, is strictly less than walk length times family size. Vertices may repeat. No S3 assumption is used.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_strict_half_separator_acyclic_cover_closed_walk
    (m n : ℕ) (hn : 0 < n) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hsep : ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a) :
    ∃ l : ℕ, 0 < l ∧ ∃ v : ℕ → Fin m,
      v l = v 0 ∧ (∀ i < l, R (v i) (v (i+1))) ∧
      2 * (∑ i ∈ range l, (univ.filter fun j => v i ∈ U j).card) < l*n := by
  classical
  obtain ⟨w₀,hw₀,hsep₀⟩ := hsep
  obtain ⟨w₁,hw₁⟩ := condorcet_finite_strict_separator_integer_weights m
    (fun A => WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val)) w₀ hw₀ hsep₀
  obtain ⟨w,hw,hHall⟩ := condorcet_integer_acyclic_separator_neighbor_mass m R w₁ hw₁
  obtain ⟨e,he⟩ := condorcet_integer_neighbor_mass_clone_permutation m R w hHall
  let V := Σ a : Fin m, Fin (w a)
  let z : Fin m → ℝ := fun a => ((univ.filter fun j => a ∈ U j).card : ℝ)
  let c : V → ℝ := fun x => 2*z x.1 - n
  have hstrict : (∑ j : Fin n, 2 * (∑ a ∈ U j, (w a : ℝ))) <
      ∑ _j : Fin n, ∑ a, (w a : ℝ) := by
    apply sum_lt_sum
    · intro j hj
      exact_mod_cast (hw (U j) (hU j)).le
    · refine ⟨⟨0,hn⟩,mem_univ _,?_⟩
      exact_mod_cast hw (U ⟨0,hn⟩) (hU ⟨0,hn⟩)
  have hswap : (∑ j : Fin n, 2 * (∑ a ∈ U j, (w a : ℝ))) =
      ∑ a, (w a : ℝ) * (2*z a) := by
    have hconvert : (∑ j : Fin n, ∑ a ∈ U j, (w a : ℝ)) =
        ∑ j : Fin n, ∑ a : Fin m, if a ∈ U j then (w a : ℝ) else 0 := by
      apply sum_congr rfl
      intro j hj
      exact (Fintype.sum_ite_mem (U j) (fun a => (w a : ℝ))).symm
    rw [← mul_sum,hconvert,sum_comm,mul_sum]
    apply sum_congr rfl
    intro a ha
    simp [z,← sum_filter]
    ring
  rw [hswap] at hstrict
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hstrict
  have hc : (∑ x : V, c x) < 0 := by
    have heq : (∑ x : V, c x) =
        (∑ a, (w a : ℝ) * (2*z a)) - (n : ℝ) * ∑ a, (w a : ℝ) := by
      rw [Fintype.sum_sigma]
      simp only [c,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_sub]
      rw [sum_sub_distrib,← sum_mul]
      ring
    rw [heq]
    linarith
  obtain ⟨l,hl,x,hclose,hneg⟩ := condorcet_permutation_negative_closed_walk e c hc
  let v : ℕ → Fin m := fun i => ((e^i) x).1
  refine ⟨l,hl,v,?_,?_,?_⟩
  · simpa only [v,pow_zero,Equiv.Perm.one_apply] using congrArg Sigma.fst hclose
  · intro i hi
    have h := he ((e^i) x)
    simpa only [v,pow_succ',Equiv.Perm.mul_apply] using h
  · have hlt : 2 * (∑ i ∈ range l, (z (v i))) < (l : ℝ)*n := by
      change (∑ i ∈ range l, (2*z (v i) - n)) < 0 at hneg
      simp only [sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at hneg
      linarith
    dsimp only [z] at hlt
    exact_mod_cast hlt
