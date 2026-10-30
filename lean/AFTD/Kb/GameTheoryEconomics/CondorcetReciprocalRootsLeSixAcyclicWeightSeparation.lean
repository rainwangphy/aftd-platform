import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicHalfCoverReciprocalRootsGeSeven
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation

/-!
# condorcet_reciprocal_roots_le_six_acyclic_weight_separation

Topic: social_choice   Node: 921315f33d47

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. General consequence of the IN-372 seven-signature lemma, motivated by product-factor screening9520/9524. ReciprocalRoots.lean checked before official submission. No new election bound or research novelty is claimed.

An S3 finite relation has nonnegative real weights putting every induced acyclic subset strictly below half if all vertices are connected by reciprocal paths to at most six designated roots and every root has a reciprocal neighbor. There is no vertex-count bound. This is a sufficient structural condition, not a proof for arbitrary oriented S3 relations.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_reciprocal_roots_le_six_acyclic_weight_separation
    (m c : ℕ) (hc : c ≤ 6) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (r : Fin c → Fin m) (label : Fin m → Fin c)
    (hpath : ∀ a, Relation.ReflTransGen (fun x y => R x y ∧ R y x) (r (label a)) a)
    (hne : ∀ j, ∃ b, R (r j) b ∧ R b (r j)) :
    ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a := by
  classical
  apply (condorcet_half_cover_acyclic_half_cover_duality m R).mp
  rintro ⟨n,U,hn,hU,hhalf⟩
  have h := condorcet_acyclic_half_cover_reciprocal_roots_ge_seven
    m n c hn R U hroot hU hhalf r label hpath hne
  omega
