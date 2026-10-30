import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_acyclic_cover_no_winning_k

Topic: social_choice   Node: 8ffbfe9417a1

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural verification of the maximum-potential neighborhood route suggested in IN-380. Generalization of the existing acyclic-cover reduction, whose strict election definition is from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . No new election bound or research novelty is claimed.

For any voter count n and committee bound k, a finite relation having outside common predecessors for all sets of at most k vertices, together with n induced acyclic sets covering each vertex at least half the time, yields an election with those n voters and no strict Condorcet winning set of size at most k. No positivity assumption on n is needed for this implication.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_acyclic_cover_no_winning_k
    (n m k : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ S : Finset (Fin m), S.card ≤ k →
      ∃ a, a ∉ S ∧ ∀ c ∈ S, R a c)
    (hacyclic : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2*(univ.filter fun v => a∈U v).card) :
    ∃ P : Fin n → Equiv.Perm (Fin m),
      ∀ S : Finset (Fin m), S.card ≤ k → ¬ is_condorcet_winning_set P S := by
  classical
  have horders : ∀ v, ∃ σ : Equiv.Perm (Fin m),
      ∀ a b, a∈U v → R a b → σ a < σ b := by
    intro v
    obtain ⟨σ,hσ⟩ := condorcet_acyclic_cover_ranking_of_wellFounded m
      (fun a b => a∈U v ∧ R a b)
      (condorcet_acyclic_cover_wellFounded_sources R {a | a∈U v} (hacyclic v))
    exact ⟨σ,fun a b ha hab => hσ a b ⟨ha,hab⟩⟩
  choose P hP using horders
  refine ⟨P,?_⟩
  intro S hS hwin
  obtain ⟨a,ha,hdom⟩ := hroot S hS
  have hsub : (univ.filter fun v => a∈U v) ⊆
      (univ.filter fun v => ∀ c∈S,P v a < P v c) := by
    intro v hv
    refine mem_filter.mpr ⟨mem_univ v,?_⟩
    intro c hc
    exact hP v a c (mem_filter.mp hv).2 (hdom c hc)
  exact (not_lt_of_ge ((hhalf a).trans (Nat.mul_le_mul_left 2 (card_le_card hsub))))
    (hwin a ha)
