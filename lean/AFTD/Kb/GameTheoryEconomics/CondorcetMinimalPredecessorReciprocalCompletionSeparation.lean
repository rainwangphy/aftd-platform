import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorReciprocalCompletionExclusion
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation

/-!
# condorcet_minimal_predecessor_reciprocal_completion_separation

Topic: social_choice   Node: 13f083318b9a

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

Under the preceding minimal-core and reciprocal-repair hypotheses, nonnegative real vertex weights on the larger relation put every induced acyclic subset strictly below half the total. This excludes the entire reciprocal completion construction for arbitrary core size, but does not handle arbitrary S3 relations.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_minimal_predecessor_reciprocal_completion_separation
    (m q k : ℕ) (hk : 0 < k)
    (R : Fin m → Fin m → Prop) (H : Fin q → Fin q → Prop) (f : Fin m → Fin q)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (hmap : ∀ a b, R a b → H (f a) (f b))
    (hrepair : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) →
      ∃ x : Fin q, ∀ a ∈ T, H x (f a) ∧ H (f a) x) :
    ∃ w : Fin q → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin q),
        WellFounded (fun a b : {a : Fin q // a∈A} => H a.val b.val) →
        2*(∑ a∈A,w a) < ∑ a,w a := by
  classical
  apply (condorcet_half_cover_acyclic_half_cover_duality q H).mp
  rintro ⟨n,U,hn,hU,hhalf⟩
  exact condorcet_minimal_predecessor_reciprocal_completion_exclusion
    m q n k hn hk R H f hroot hminimal hmap hrepair U hU hhalf
