import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicCoverNoWinningK
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicHalfCoverOfNoWinningK
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_failure_k_iff_acyclic_half_cover

Topic: social_choice   Node: bb532fcc1c9f

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural verification of the maximum-potential neighborhood route suggested in IN-380. Generalization of the existing acyclic-cover reduction, whose strict election definition is from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . No new election bound or research novelty is claimed.

For fixed voter count n and committee bound k, some finite n-voter election has no strict Condorcet winning committee of size at most k if and only if some finite relation has outside common predecessors for sets of size at most k and admits n induced acyclic sets covering every vertex at least half the time. This generalizes the existing k=3 equivalence and proves neither existence nor nonexistence of such objects.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_failure_k_iff_acyclic_half_cover (n k : ℕ) :
    (∃ (m : ℕ) (P : Fin n → Equiv.Perm (Fin m)),
      ∀ S : Finset (Fin m), S.card ≤ k → ¬is_condorcet_winning_set P S) ↔
    (∃ (q : ℕ) (R : Fin q → Fin q → Prop) (U : Fin n → Finset (Fin q)),
      (∀ J : Finset (Fin q), J.card ≤ k → ∃ a, a∉J ∧ ∀ b∈J, R a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin q // a∈U v} => R a.val b.val)) ∧
      (∀ a, n ≤ 2*(univ.filter fun v => a∈U v).card)) := by
  constructor
  · rintro ⟨m,P,hP⟩
    exact condorcet_acyclic_half_cover_of_no_winning_k n m k P hP
  · rintro ⟨q,R,U,hroot,hacyclic,hhalf⟩
    obtain ⟨P,hP⟩ := condorcet_acyclic_cover_no_winning_k n q k R U hroot hacyclic hhalf
    exact ⟨q,P,hP⟩
