import AFTD.Prelude

/-!
# condorcet_half_coalitions_partition_of_incompatible

Topic: social_choice   Node: 16121c32070f

Provenance: helper lemma. IN-339 supporting step for the OP-19 campaign. Strict definition: Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related selector formulation: arXiv:2604.19851v2. These are verification and coalition-closure helpers; no new dimension bound or research advance is asserted.

For two incompatible voter events in a finite electorate, if each has at least half of the voter support, the electorate size is even, the two support sizes are equal, and the events are exact complements for every voter. This logical form can be applied after pooling challenger claims.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_coalitions_partition_of_incompatible
    (n : ℕ) (A B : Fin n → Prop) [DecidablePred A] [DecidablePred B]
    (hA : n ≤ 2 * (univ.filter A).card)
    (hB : n ≤ 2 * (univ.filter B).card)
    (hinc : ∀ v, ¬(A v ∧ B v)) :
    Even n ∧ (univ.filter A).card = (univ.filter B).card ∧
      ∀ v, A v ↔ ¬ B v := by
  let U := univ.filter A
  let V := univ.filter B
  change n ≤ 2 * U.card at hA
  change n ≤ 2 * V.card at hB
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvV
    exact hinc v ⟨(mem_filter.mp hvU).2, (mem_filter.mp hvV).2⟩
  have hc : U.card + V.card ≤ n := by
    rw [← card_union_of_disjoint hd]
    simpa only [card_univ, Fintype.card_fin] using card_le_univ (U ∪ V)
  have heq : U.card + V.card = n := by omega
  have hfull : U ∪ V = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simpa only [card_univ, Fintype.card_fin, card_union_of_disjoint hd, heq]
      using Nat.le_refl n
  refine ⟨⟨U.card, by omega⟩, ?_, ?_⟩
  · change U.card = V.card
    omega
  · intro v
    have hv : v ∈ U ↔ v ∉ V := by
      constructor
      · intro hu hv
        exact disjoint_left.mp hd hu hv
      · intro hv
        have hu : v ∈ U ∪ V := by rw [hfull]; exact mem_univ v
        exact (mem_union.mp hu).resolve_right hv
    simpa only [U, V, mem_filter, mem_univ, true_and] using hv

-- Equality of voter coalitions lets us pool all their preference constraints.
-- Each nonempty selected root subfamily must have a sink in that partial order.
