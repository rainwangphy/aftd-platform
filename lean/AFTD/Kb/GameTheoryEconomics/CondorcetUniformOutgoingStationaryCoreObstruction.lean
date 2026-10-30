import AFTD.Prelude

/-!
# condorcet_uniform_outgoing_stationary_core_obstruction

Topic: social_choice   Node: 74a17d54bcd4

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. Experiments9470,9472,9474 and UniformOutgoingObstruction.lean. Supporting diagnostic for the main route; no new election bound or research novelty is claimed.

An explicit eight-vertex S3 relation is globally minimal under induced vertex restriction and every arrow has a private triple. Its positive integer circulation giving equal occupation to all outgoing arrows from each vertex has an acyclic subset of mass124248 out of247818, strictly more than half. Nevertheless alternative nonnegative integer weights totaling13 place every acyclic subset at mass at most4. Thus canonical uniform-outgoing transition weights can fail even after both core reductions. This is not an election counterexample and makes no orientedness assertion.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

def condorcet_uniform_outgoing_gap_pred : Fin 8 → ℕ := ![148,148,249,87,206,146,167,62]
def condorcet_uniform_outgoing_gap_relation (a b : Fin 8) : Prop :=
  (condorcet_uniform_outgoing_gap_pred b).testBit a.val = true
instance : DecidableRel condorcet_uniform_outgoing_gap_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_uniform_outgoing_gap_pred b).testBit a.val = true))
def condorcet_uniform_outgoing_gap_neighbors (a : Fin 8) : Finset (Fin 8) :=
  univ.filter (fun b => condorcet_uniform_outgoing_gap_relation a b)
def condorcet_uniform_outgoing_gap_occupation : Fin 8 → ℕ := ![6865,4119,7878,11905,6684,5612,10169,6033]
def condorcet_uniform_outgoing_gap_weight (a : Fin 8) : ℕ :=
  (condorcet_uniform_outgoing_gap_neighbors a).card * condorcet_uniform_outgoing_gap_occupation a
def condorcet_uniform_outgoing_gap_set : Finset (Fin 8) := {0,1,5,6,3}
def condorcet_uniform_outgoing_gap_order : Fin 8 → ℕ := ![0,1,0,4,0,2,3,0]
def condorcet_uniform_outgoing_gap_private : Fin 8 → Finset (Finset (Fin 8)) :=
  ![{{2,3,6}},{{3,4,5},{3,5,6},{4,5,7},{5,6,7}},{{0,3,4},{0,3,6},{0,4,7},{0,6,7},{1,3,4},{1,3,6},{1,4,7},{1,6,7}},{{2,4,7}},{{0,2,3},{0,2,7},{0,3,5},{0,5,7},{1,2,3},{1,2,7},{1,3,5},{1,5,7},{2,3,5},{2,3,7},{2,5,7}},{{2,6,7}},{{2,3,4}},{{0,2,4},{0,2,6},{0,4,5},{0,5,6},{1,2,4},{1,2,6},{1,4,5},{1,5,6},{2,4,5},{2,4,6},{2,5,6}}]
def condorcet_uniform_outgoing_gap_separator : Fin 8 → ℕ := ![1,0,4,2,3,0,1,2]
def condorcet_uniform_outgoing_gap_forbidden : Finset (Finset (Fin 8)) :=
  {{0,2},{2,3},{1,4},{2,4},{3,4},{1,2,5},{2,6},{0,4,6},{4,5,6},{1,7},{2,7},{0,3,7},{4,7},{5,7},{3,6,7}}

theorem condorcet_uniform_outgoing_gap_s3 :
    ∀ J : Finset (Fin 8), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_uniform_outgoing_gap_relation a b := by decide

theorem condorcet_uniform_outgoing_gap_proper_check :
    ∀ S : Finset (Fin 8), S ≠ univ →
      ∃ J : Finset (Fin 8), J ⊆ S ∧ J.card ≤ 3 ∧
        ∀ a ∈ S, ∃ b ∈ J, ¬condorcet_uniform_outgoing_gap_relation a b := by decide

theorem condorcet_uniform_outgoing_gap_global_core
    (S : Finset (Fin 8))
    (hS : ∀ J : Finset (Fin 8), J ⊆ S → J.card ≤ 3 →
      ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, condorcet_uniform_outgoing_gap_relation a b) : S = univ := by
  by_contra hne
  obtain ⟨J,hJS,hJ,hbad⟩ := condorcet_uniform_outgoing_gap_proper_check S hne
  obtain ⟨a,ha,_,hroot⟩ := hS J hJS hJ
  obtain ⟨b,hb,hab⟩ := hbad a ha
  exact hab (hroot b hb)

theorem condorcet_uniform_outgoing_gap_private_check :
    (∀ a, ∀ J ∈ condorcet_uniform_outgoing_gap_private a,
      J.card = 3 ∧ a ∉ J ∧
      (∀ b ∈ J, condorcet_uniform_outgoing_gap_relation a b) ∧
      ∀ r, (∀ b ∈ J, condorcet_uniform_outgoing_gap_relation r b) → r = a) ∧
    (∀ a b, condorcet_uniform_outgoing_gap_relation a b →
      ∃ J ∈ condorcet_uniform_outgoing_gap_private a, b ∈ J) := by decide

theorem condorcet_uniform_outgoing_gap_flow_check :
    (∀ a, 0 < condorcet_uniform_outgoing_gap_occupation a) ∧
    (∀ b, condorcet_uniform_outgoing_gap_weight b =
      ∑ a : Fin 8, if condorcet_uniform_outgoing_gap_relation a b then
        condorcet_uniform_outgoing_gap_occupation a else 0) ∧
    (∑ a : Fin 8, condorcet_uniform_outgoing_gap_weight a) = 247818 ∧
    (∑ a ∈ condorcet_uniform_outgoing_gap_set, condorcet_uniform_outgoing_gap_weight a) = 124248 := by decide

theorem condorcet_uniform_outgoing_gap_order_check :
    ∀ a b : Fin 8,
      a ∈ condorcet_uniform_outgoing_gap_set → b ∈ condorcet_uniform_outgoing_gap_set →
      condorcet_uniform_outgoing_gap_relation a b →
      condorcet_uniform_outgoing_gap_order a < condorcet_uniform_outgoing_gap_order b := by decide

theorem condorcet_uniform_outgoing_gap_acyclic :
    WellFounded (fun a b : {a : Fin 8 // a ∈ condorcet_uniform_outgoing_gap_set} =>
      condorcet_uniform_outgoing_gap_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 8 // a ∈ condorcet_uniform_outgoing_gap_set} =>
    condorcet_uniform_outgoing_gap_order a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_uniform_outgoing_gap_order_check a b a.property b.property hab

theorem condorcet_uniform_outgoing_gap_forbidden_check :
    ∀ B ∈ condorcet_uniform_outgoing_gap_forbidden,
      B.Nonempty ∧ ∀ a ∈ B, ∃ b ∈ B, condorcet_uniform_outgoing_gap_relation b a := by decide

theorem condorcet_uniform_outgoing_gap_separator_check :
    ∀ A : Finset (Fin 8),
      (∀ B ∈ condorcet_uniform_outgoing_gap_forbidden, ¬B ⊆ A) →
        (∑ a ∈ A, condorcet_uniform_outgoing_gap_separator a) ≤ 4 := by decide

theorem condorcet_uniform_outgoing_gap_separates
    (A : Finset (Fin 8))
    (hA : WellFounded (fun a b : {a : Fin 8 // a ∈ A} => condorcet_uniform_outgoing_gap_relation a.val b.val)) :
    2 * (∑ a ∈ A, condorcet_uniform_outgoing_gap_separator a) <
      ∑ a : Fin 8, condorcet_uniform_outgoing_gap_separator a := by
  have hsum : (∑ a : Fin 8, condorcet_uniform_outgoing_gap_separator a) = 13 := by decide
  rw [hsum]
  have hbound : (∑ a ∈ A, condorcet_uniform_outgoing_gap_separator a) ≤ 4 := by
    apply condorcet_uniform_outgoing_gap_separator_check A
    intro B hB hsub
    obtain ⟨hne,hpred⟩ := condorcet_uniform_outgoing_gap_forbidden_check B hB
    obtain ⟨b,hb⟩ := hne
    obtain ⟨a,ha,hmin⟩ := hA.has_min {a : {a : Fin 8 // a ∈ A} | a.val ∈ B} ⟨⟨b,hsub hb⟩,hb⟩
    obtain ⟨c,hc,hca⟩ := hpred a.val ha
    exact hmin ⟨c,hsub hc⟩ hc hca
  omega

theorem condorcet_uniform_outgoing_stationary_core_obstruction :
    (∀ J : Finset (Fin 8), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, condorcet_uniform_outgoing_gap_relation a b) ∧
    (∀ S : Finset (Fin 8),
      (∀ J : Finset (Fin 8), J ⊆ S → J.card ≤ 3 →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, condorcet_uniform_outgoing_gap_relation a b) → S = univ) ∧
    (∀ a b, condorcet_uniform_outgoing_gap_relation a b →
      ∃ J ∈ condorcet_uniform_outgoing_gap_private a, b ∈ J ∧ J.card = 3 ∧
        (∀ c ∈ J, condorcet_uniform_outgoing_gap_relation a c) ∧
        ∀ r, (∀ c ∈ J, condorcet_uniform_outgoing_gap_relation r c) → r = a) ∧
    (∀ a, 0 < condorcet_uniform_outgoing_gap_occupation a) ∧
    (∀ b, condorcet_uniform_outgoing_gap_weight b =
      ∑ a : Fin 8, if condorcet_uniform_outgoing_gap_relation a b then condorcet_uniform_outgoing_gap_occupation a else 0) ∧
    WellFounded (fun a b : {a : Fin 8 // a ∈ condorcet_uniform_outgoing_gap_set} =>
      condorcet_uniform_outgoing_gap_relation a.val b.val) ∧
    ((∑ a : Fin 8, condorcet_uniform_outgoing_gap_weight a) <
      2 * (∑ a ∈ condorcet_uniform_outgoing_gap_set, condorcet_uniform_outgoing_gap_weight a)) ∧
    (∀ A : Finset (Fin 8), WellFounded (fun a b : {a : Fin 8 // a ∈ A} =>
      condorcet_uniform_outgoing_gap_relation a.val b.val) →
      2 * (∑ a ∈ A, condorcet_uniform_outgoing_gap_separator a) <
        ∑ a : Fin 8, condorcet_uniform_outgoing_gap_separator a) := by
  refine ⟨condorcet_uniform_outgoing_gap_s3,condorcet_uniform_outgoing_gap_global_core,?_,
    condorcet_uniform_outgoing_gap_flow_check.1,condorcet_uniform_outgoing_gap_flow_check.2.1,
    condorcet_uniform_outgoing_gap_acyclic,?_,condorcet_uniform_outgoing_gap_separates⟩
  · intro a b hab
    obtain ⟨J,hJ,hb⟩ := condorcet_uniform_outgoing_gap_private_check.2 a b hab
    obtain ⟨hcard,hnot,hroot,hprivate⟩ := condorcet_uniform_outgoing_gap_private_check.1 a J hJ
    exact ⟨J,hJ,hb,hcard,hroot,hprivate⟩
  · rw [condorcet_uniform_outgoing_gap_flow_check.2.2.1,condorcet_uniform_outgoing_gap_flow_check.2.2.2]
    decide
