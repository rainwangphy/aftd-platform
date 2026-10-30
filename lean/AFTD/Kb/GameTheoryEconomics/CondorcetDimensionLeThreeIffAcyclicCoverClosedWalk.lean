import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetStrictHalfSeparatorAcyclicCoverClosedWalk
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_dimension_le_three_iff_acyclic_cover_closed_walk

Topic: social_choice   Node: 42c0cd83f597

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. Supporting reduction from the proved strict-half circulation bridge. Scratch ClosedWalk.lean passed trusted-axiom checking. Standard finite matching and orbit averaging; no research novelty or new election bound is claimed.

The universal strict Condorcet bound three is equivalent to the following statement: on every finite S3 directed relation, every positive finite family of induced acyclic subsets admits a nonempty closed directed walk whose average membership count is strictly below half the family size. Walks may repeat vertices. This is an equivalent formulation, not a proof of the S3 walk-existence assertion.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_dimension_le_three_iff_acyclic_cover_closed_walk
    : (∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)), 0 < n →
        ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S) ↔
      (∀ (m n : ℕ) (R : Fin m → Fin m → Prop)
        (U : Fin n → Finset (Fin m)), 0 < n →
        (∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) →
        (∀ j, WellFounded (fun a b : {a : Fin m // a ∈ U j} => R a.val b.val)) →
        ∃ l : ℕ, 0 < l ∧ ∃ v : ℕ → Fin m,
          v l = v 0 ∧ (∀ i < l, R (v i) (v (i+1))) ∧
          2 * (∑ i ∈ range l, (univ.filter fun j => v i ∈ U j).card) < l*n) := by
  classical
  constructor
  · intro hmain m n R U hn hroot hU
    exact condorcet_strict_half_separator_acyclic_cover_closed_walk m n hn R U hU
      (condorcet_dimension_le_three_iff_acyclic_weight_separation.mp hmain m R hroot)
  · intro hwalk
    apply condorcet_dimension_le_three_iff_acyclic_weight_separation.mpr
    intro m R hroot
    apply (condorcet_half_cover_acyclic_half_cover_duality m R).mp
    rintro ⟨n,U,hn,hU,hhalf⟩
    obtain ⟨l,hl,v,hclose,hedges,hlt⟩ := hwalk m n R U hn hroot hU
    have hle : l*n ≤ 2 * (∑ i ∈ range l, (univ.filter fun j => v i ∈ U j).card) := by
      calc
        l*n = ∑ i ∈ range l, n := by simp
        _ ≤ ∑ i ∈ range l, 2 * (univ.filter fun j => v i ∈ U j).card :=
          sum_le_sum (fun i hi => hhalf (v i))
        _ = _ := by rw [mul_sum]
    omega
