import AFTD.Prelude
import AFTD.Kb.Tcs.WildTwoMatchingsSmallClosedSetsDisjointOrEqual

/-!
# wild_two_matchings_six_closed_family_bound

Topic: graphs   Node: c3ef18ac7e46

Provenance: helper lemma. IN-374 / OP-306, dependence estimates for the weighted partition route to https://arxiv.org/html/2610.22142v1. Elementary matching support consequence of the standard even-cycle decomposition of two disjoint perfect matchings; matching background https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content . Exact experiment9362 audits six saved15 arrays and cyclic9,13,21,27,39,61. No new wild-number bound, sharpness case or research advance is claimed.

A finite family F of six-element subsets of U, closed under two involutions whose actions on each member are fixed-point-free and distinct at every vertex, satisfies 6*card(F)<=card(U). This follows from pairwise disjointness and finite union cardinality.
-/

open Finset

theorem wild_two_matchings_six_closed_family_bound
    {α : Type*} [DecidableEq α] (f g : α → α)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (F : Finset (Finset α)) (U : Finset α)
    (hsize : ∀ S ∈ F, S.card = 6)
    (hsub : ∀ S ∈ F, S ⊆ U)
    (hc : ∀ S ∈ F, ∀ x ∈ S, f x ∈ S ∧ g x ∈ S)
    (hn : ∀ S ∈ F, ∀ x ∈ S, f x ≠ x ∧ g x ≠ x ∧ f x ≠ g x) :
    6 * F.card ≤ U.card := by
  have hd : (F : Set (Finset α)).PairwiseDisjoint id := by
    intro S hS T hT hne
    have h := wild_two_matchings_small_closed_sets_disjoint_or_equal f g hf hg
      S T (by rw [hsize S hS]; omega) (by rw [hsize T hT]; omega)
      (hc S hS) (hc T hT) (by
        intro x hx
        rcases mem_union.mp hx with hx | hx
        · exact hn S hS x hx
        · exact hn T hT x hx)
    exact h.resolve_right hne
  have hcard : (F.biUnion id).card = 6 * F.card := by
    rw [Finset.card_biUnion hd]
    simp only [id_eq]
    rw [Finset.sum_const_nat hsize, Nat.mul_comm]
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
  exact hsub S hS hxS
