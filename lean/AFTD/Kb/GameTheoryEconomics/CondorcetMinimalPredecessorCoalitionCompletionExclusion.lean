import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorAcyclicCut
import AFTD.Kb.GameTheoryEconomics.CondorcetHalfCoalitionsPartitionOfIncompatible

/-!
# condorcet_minimal_predecessor_coalition_completion_exclusion

Topic: social_choice   Node: 32c6a0fab863

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

Such a globally minimal predecessor core cannot have an acyclic half-cover if every undominated (k+1)-set has an additional event of at least half the voters avoiding every member of that set. The extra event hypothesis is essential.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_minimal_predecessor_coalition_completion_exclusion
    (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (U : Fin n → Finset (Fin m))
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2*(univ.filter fun v => a∈U v).card)
    (hextra : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) →
      ∃ B : Finset (Fin n), n ≤ 2*B.card ∧ ∀ v ∈ B, ∀ a ∈ T, a ∉ U v) : False := by
  classical
  obtain ⟨r,_,_⟩ := hroot ∅ (by simp)
  have hpos : 0 < (univ.filter fun v => r ∈ U v).card := by
    have h := hhalf r
    omega
  obtain ⟨v,hv⟩ := card_pos.mp hpos
  obtain ⟨T,hTcard,hTbad,⟨a,haT,haU⟩,⟨b,hbT,hbU⟩⟩ :=
    condorcet_minimal_predecessor_acyclic_cut m k hk R hroot hminimal (U v)
      ⟨r,(mem_filter.mp hv).2⟩ (hU v)
  obtain ⟨B,hB,havoid⟩ := hextra T hTcard hTbad
  have hB' : n ≤ 2*(univ.filter fun v => v ∈ B).card := by simpa using hB
  have ha := (condorcet_half_coalitions_partition_of_incompatible n
    (fun v => a ∈ U v) (fun v => v ∈ B) (hhalf a) hB'
    (fun v hv => havoid v hv.2 a haT hv.1)).2.2
  have hb := (condorcet_half_coalitions_partition_of_incompatible n
    (fun v => b ∈ U v) (fun v => v ∈ B) (hhalf b) hB'
    (fun v hv => havoid v hv.2 b hbT hv.1)).2.2
  exact hbU ((hb v).mpr ((ha v).mp haU))
