import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetPotentialMaximumNeighborhoodHalfCover
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicCoverNoWinningK
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_potential_break_of_fixed_electorate_bound

Topic: social_choice   Node: 8b0991fd8a47

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural verification of the maximum-potential neighborhood route suggested in IN-380. Generalization of the existing acyclic-cover reduction, whose strict election definition is from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . No new election bound or research novelty is claimed.

Assume every finite election with exactly n voters has a strict Condorcet winning committee of size at most k. Then on any finite relation with outside common predecessors for sets of size at most k+1, any family of n induced acyclic sets and any real potential have an arrow a to b with 2*coverage(a)+h(a) < n+h(b). The fixed-electorate election bound is an explicit hypothesis, not a result of this theorem.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_potential_break_of_fixed_electorate_bound
    (n k : ℕ)
    (hbound : ∀ (m : ℕ) (P : Fin n → Equiv.Perm (Fin m)),
      ∃ S : Finset (Fin m), S.card ≤ k ∧ is_condorcet_winning_set P S)
    (m : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m)) (h : Fin m → ℝ)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k+1 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) :
    ∃ a b, R a b ∧
      2*((univ.filter fun v => a∈U v).card : ℝ)+h a < (n : ℝ)+h b := by
  classical
  by_contra hbad
  push_neg at hbad
  obtain ⟨q,Q,W,hQ,hW,hcover⟩ :=
    condorcet_potential_maximum_neighborhood_half_cover m n k R U h hroot hU hbad
  obtain ⟨P,hP⟩ := condorcet_acyclic_cover_no_winning_k n q k Q W hQ hW hcover
  obtain ⟨S,hS,hwin⟩ := hbound q P
  exact hP S hS hwin
