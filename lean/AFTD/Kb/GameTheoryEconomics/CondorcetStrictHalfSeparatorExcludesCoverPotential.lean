import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStrictHalfSeparatorIffIntegerCirculation
import AFTD.Kb.GameTheoryEconomics.CondorcetEdgeCirculationDualBound

/-!
# condorcet_strict_half_separator_excludes_cover_potential

Topic: social_choice   Node: 213ba6ae9b82

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

Let a finite directed relation have a nonnegative real strict-half separator. For every positive number n of induced acyclic vertex subsets U and every real vertex potential h, some arrow a to b satisfies 2 times the number of subsets containing a plus h(a) strictly less than n plus h(b). The U family is arbitrary and need not cover any vertex.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_strict_half_separator_excludes_cover_potential
    (m n : ℕ) (hn : 0 < n) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m)) (h : Fin m → ℝ)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hsep : ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a) :
    ∃ a b, R a b ∧
      2 * ((univ.filter fun v => a ∈ U v).card : ℝ) + h a < (n : ℝ) + h b := by
  classical
  obtain ⟨f,hf,hbalance,hacyc⟩ :=
    (condorcet_strict_half_separator_iff_integer_circulation m R).mp hsep
  let w : Fin m → ℝ := fun a => ∑ b, (f a b : ℝ)
  let c : Fin m → ℝ := fun a => ((univ.filter fun v => a ∈ U v).card : ℝ)
  by_contra hbad
  push_neg at hbad
  have hlocal : ∀ a b, R a b → (n : ℝ) + h b ≤ 2*c a + h a := by
    intro a b hab
    exact hbad a b hab
  have hdual := condorcet_edge_circulation_dual_bound m R
    (fun a b => (f a b : ℝ)) (fun a => 2*c a) h n
    (by intro a b; positivity)
    (by intro a b hab; simp [hf a b hab])
    (by intro a; exact_mod_cast hbalance a) hlocal
  have hstrict : (∑ v : Fin n, 2 * (∑ a ∈ U v, w a)) <
      ∑ _v : Fin n, ∑ a, w a := by
    apply sum_lt_sum
    · intro v hv
      have hlt : 2 * (∑ a ∈ U v, w a) < ∑ a, w a := by
        dsimp only [w]
        exact_mod_cast hacyc (U v) (hU v)
      exact hlt.le
    · refine ⟨⟨0,hn⟩,mem_univ _,?_⟩
      dsimp only [w]
      exact_mod_cast hacyc (U ⟨0,hn⟩) (hU ⟨0,hn⟩)
  have hswap : (∑ v : Fin n, 2 * (∑ a ∈ U v, w a)) =
      ∑ a, w a * (2*c a) := by
    have hconvert : (∑ v : Fin n, ∑ a ∈ U v, w a) =
        ∑ v : Fin n, ∑ a : Fin m, if a ∈ U v then w a else 0 := by
      apply sum_congr rfl
      intro v hv
      exact (Fintype.sum_ite_mem (U v) w).symm
    rw [← mul_sum,hconvert,sum_comm]
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    simp [c,← sum_filter]
    ring
  rw [hswap] at hstrict
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hstrict
  exact (not_lt_of_ge hdual) hstrict
