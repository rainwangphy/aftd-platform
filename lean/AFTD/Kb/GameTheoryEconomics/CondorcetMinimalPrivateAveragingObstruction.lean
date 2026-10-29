import AFTD.Prelude

/-!
# condorcet_minimal_private_averaging_obstruction

Topic: social_choice   Node: 90025ad1cc27

Provenance: helper lemma. IN-362 method diagnostic for OP-19. The proposed complete-private-triple averaging construction was left open on GLOBAL minimum cores in IN-357. Exact data from experiments9013 and9016; both vertex and arc minimality are checked. This is no election counterexample, no failure of optimized policies, and no research advance.

There exist an irreflexive directed relation R on eight vertices, nonempty complete families F(a) of private three-element sets at each root, strictly positive natural per-triple occupations q, and an induced acyclic set U. Every ordered triple has a common predecessor. Every induced subset retaining the outside-predecessor property for all sets of size at most three is the entire vertex set, so this is a GLOBAL minimum core. Every arrow from a to b is contained in some member of F(a), making every arrow indispensable. Each private triple excludes its root and has that root as its unique common predecessor; completeness is checked for all increasing triples. The weights w(a)=card(F(a))*q(a) satisfy the exact uniform-private averaging stationarity equation 3*w(b)=sum over a and J in F(a) containing b of q(a). Their total is952908 and U has weight496506, strictly above half. Thus global core reduction and arc minimization do not repair this particular averaging rule.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

def condorcet_minimal_private_pred : Fin 8 → ℕ := ![126,156,184,208,231,200,155,125]
def condorcet_minimal_private_relation (a b : Fin 8) : Prop :=
  (condorcet_minimal_private_pred b).testBit a.val = true
instance : DecidableRel condorcet_minimal_private_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_minimal_private_pred b).testBit a.val = true))
def condorcet_minimal_private_list : Fin 8 → List (Finset (Fin 8)) := ![[{4,6,7}],[{0,4,6}],[{0,1,4},{1,4,7}],[{0,1,5},{0,2,5},{0,5,6},{1,5,7},{2,5,7},{5,6,7}],[{0,1,3},{0,2,3},{0,3,6},{1,3,7},{2,3,7},{3,6,7}],[{0,2,4},{2,4,7}],[{0,3,4},{0,3,5},{0,4,5},{3,4,7},{3,5,7},{4,5,7}],[{1,2,4},{1,3,4},{1,3,5},{1,4,5},{1,4,6},{2,3,4},{2,3,5},{2,4,5},{2,4,6},{3,4,6},{3,5,6},{4,5,6}]]
def condorcet_minimal_private_family (a : Fin 8) : Finset (Finset (Fin 8)) :=
  (condorcet_minimal_private_list a).toFinset
def condorcet_minimal_private_occupation : Fin 8 → ℕ := ![127396,81544,41755,19108,31728,44704,20559,11890]
def condorcet_minimal_private_weight (a : Fin 8) : ℕ :=
  (condorcet_minimal_private_family a).card * condorcet_minimal_private_occupation a
def condorcet_minimal_private_order : Fin 8 → ℕ := ![4,3,2,0,0,1,0,0]
def condorcet_minimal_private_set : Finset (Fin 8) := {3,5,2,1,0}

theorem condorcet_minimal_private_irreflexive : ∀ a,
    ¬condorcet_minimal_private_relation a a := by decide

theorem condorcet_minimal_private_s3 : ∀ a b c : Fin 8,
    ∃ r, condorcet_minimal_private_relation r a ∧
      condorcet_minimal_private_relation r b ∧
      condorcet_minimal_private_relation r c := by decide

theorem condorcet_minimal_private_members : ∀ a,
    (condorcet_minimal_private_family a).Nonempty ∧
    ∀ J ∈ condorcet_minimal_private_family a,
      J.card = 3 ∧ a ∉ J ∧
      (∀ b ∈ J, condorcet_minimal_private_relation a b) ∧
      ∀ r, (∀ b ∈ J, condorcet_minimal_private_relation r b) → r = a := by
  have hnonempty : ∀ a, (condorcet_minimal_private_family a).Nonempty := by decide
  have hcheck : ∀ a, (condorcet_minimal_private_list a).all (fun J =>
      decide (J.card = 3 ∧ a ∉ J ∧
        (∀ b ∈ J, condorcet_minimal_private_relation a b) ∧
        ∀ r, (∀ b ∈ J, condorcet_minimal_private_relation r b) → r = a)) = true := by
    decide
  intro a
  refine ⟨hnonempty a, ?_⟩
  intro J hJ
  have hm : J ∈ condorcet_minimal_private_list a := by
    exact List.mem_toFinset.mp hJ
  exact of_decide_eq_true (List.all_eq_true.mp (hcheck a) J hm)

theorem condorcet_minimal_private_complete_forward (r a b c : Fin 8)
    (hJ : {a, b, c} ∈ condorcet_minimal_private_family r) :
    condorcet_minimal_private_relation r a ∧
    condorcet_minimal_private_relation r b ∧
    condorcet_minimal_private_relation r c ∧
    ∀ s, (condorcet_minimal_private_relation s a ∧
      condorcet_minimal_private_relation s b ∧
      condorcet_minimal_private_relation s c) → s = r := by
  have hmem := (condorcet_minimal_private_members r).2 {a, b, c} hJ
  refine ⟨hmem.2.2.1 a (by simp), hmem.2.2.1 b (by simp), hmem.2.2.1 c (by simp), ?_⟩
  intro s ⟨hsa, hsb, hsc⟩
  apply hmem.2.2.2 s
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hsa
  · exact hsb
  · exact hsc

theorem condorcet_minimal_private_complete_backward : ∀ a b c : Fin 8, a < b → b < c → ∀ r,
    (condorcet_minimal_private_relation r a ∧
     condorcet_minimal_private_relation r b ∧
     condorcet_minimal_private_relation r c ∧
     ∀ s, (condorcet_minimal_private_relation s a ∧
           condorcet_minimal_private_relation s b ∧
           condorcet_minimal_private_relation s c) → s = r) →
    {a,b,c} ∈ condorcet_minimal_private_family r := by decide

theorem condorcet_minimal_private_complete : ∀ r a b c : Fin 8,
    a < b → b < c →
    ({a,b,c} ∈ condorcet_minimal_private_family r ↔
      condorcet_minimal_private_relation r a ∧
      condorcet_minimal_private_relation r b ∧
      condorcet_minimal_private_relation r c ∧
      ∀ s, (condorcet_minimal_private_relation s a ∧
        condorcet_minimal_private_relation s b ∧
        condorcet_minimal_private_relation s c) → s = r) := by
  intro r a b c hab hbc
  constructor
  · exact condorcet_minimal_private_complete_forward r a b c
  · exact condorcet_minimal_private_complete_backward a b c hab hbc r

theorem condorcet_minimal_private_flow : ∀ b : Fin 8,
    3 * condorcet_minimal_private_weight b =
      ∑ a : Fin 8, ∑ J ∈ condorcet_minimal_private_family a,
        if b ∈ J then condorcet_minimal_private_occupation a else 0 := by decide

theorem condorcet_minimal_private_mass :
    (∑ a : Fin 8, condorcet_minimal_private_weight a) = 952908 ∧
    (∑ a ∈ condorcet_minimal_private_set, condorcet_minimal_private_weight a) = 496506 ∧
    0 < (∑ a : Fin 8, condorcet_minimal_private_weight a) ∧
    (∑ a : Fin 8, condorcet_minimal_private_weight a) <
      2 * (∑ a ∈ condorcet_minimal_private_set, condorcet_minimal_private_weight a) := by decide

theorem condorcet_minimal_private_ordered : ∀ a b : Fin 8,
    a ∈ condorcet_minimal_private_set → b ∈ condorcet_minimal_private_set →
    condorcet_minimal_private_relation a b →
      condorcet_minimal_private_order a < condorcet_minimal_private_order b := by decide

theorem condorcet_minimal_private_wellFounded :
    WellFounded (fun a b : {a : Fin 8 // a ∈ condorcet_minimal_private_set} =>
      condorcet_minimal_private_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 8 // a ∈ condorcet_minimal_private_set} =>
    condorcet_minimal_private_order a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_minimal_private_ordered a.val b.val a.property b.property hab


theorem condorcet_minimal_private_arc_witness : ∀ a b : Fin 8,
    condorcet_minimal_private_relation a b →
    ∃ J ∈ condorcet_minimal_private_family a, b ∈ J := by decide

theorem condorcet_minimal_private_core_check : ∀ B : Finset (Fin 8),
    B.Nonempty →
    (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∃ r ∈ B,
      condorcet_minimal_private_relation r a ∧
      condorcet_minimal_private_relation r b ∧
      condorcet_minimal_private_relation r c) → B = univ := by decide

theorem condorcet_minimal_private_core : ∀ B : Finset (Fin 8),
    (∀ J : Finset (Fin 8), J ⊆ B → J.card ≤ 3 →
      ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, condorcet_minimal_private_relation a b) →
    B = univ := by
  intro B hB
  obtain ⟨r,hr,_⟩ := hB ∅ (empty_subset _) (by simp)
  apply condorcet_minimal_private_core_check B ⟨r,hr⟩
  intro a ha b hb c hc
  have hsub : ({a,b,c} : Finset (Fin 8)) ⊆ B := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨ha,hb,hc⟩
  have hcard : ({a,b,c} : Finset (Fin 8)).card ≤ 3 := by
    have h1 := card_insert_le a ({b,c} : Finset (Fin 8))
    have h2 := card_insert_le b ({c} : Finset (Fin 8))
    simp only [card_singleton] at h2
    omega
  obtain ⟨r,hr,_,hR⟩ := hB {a,b,c} hsub hcard
  exact ⟨r,hr,hR a (by simp),hR b (by simp),hR c (by simp)⟩

theorem condorcet_minimal_private_averaging_obstruction :
    ∃ (R : Fin 8 → Fin 8 → Prop)
      (F : Fin 8 → Finset (Finset (Fin 8))) (q : Fin 8 → ℕ)
      (U : Finset (Fin 8)),
      (∀ a, ¬ R a a) ∧
      (∀ a b c, ∃ r, R r a ∧ R r b ∧ R r c) ∧
      (∀ a, (F a).Nonempty ∧ ∀ J ∈ F a,
        J.card = 3 ∧ a ∉ J ∧ (∀ b ∈ J, R a b) ∧
        ∀ r, (∀ b ∈ J, R r b) → r = a) ∧
      (∀ r a b c, a < b → b < c →
        ({a,b,c} ∈ F r ↔ R r a ∧ R r b ∧ R r c ∧
          ∀ s, (R s a ∧ R s b ∧ R s c) → s = r)) ∧
      (∀ B : Finset (Fin 8),
        (∀ J : Finset (Fin 8), J ⊆ B → J.card ≤ 3 →
          ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, R a b) → B = univ) ∧
      (∀ a b, R a b → ∃ J ∈ F a, b ∈ J) ∧
      (∀ a, 0 < q a) ∧
      (∀ b, 3 * ((F b).card * q b) =
        ∑ a, ∑ J ∈ F a, if b ∈ J then q a else 0) ∧
      (∑ a, (F a).card * q a) = 952908 ∧
      (∑ a ∈ U, (F a).card * q a) = 496506 ∧
      0 < (∑ a, (F a).card * q a) ∧
      (∑ a, (F a).card * q a) < 2 * (∑ a ∈ U, (F a).card * q a) ∧
      WellFounded (fun a b : {a : Fin 8 // a ∈ U} => R a.val b.val) := by
  refine ⟨condorcet_minimal_private_relation, condorcet_minimal_private_family,
    condorcet_minimal_private_occupation, condorcet_minimal_private_set,
    condorcet_minimal_private_irreflexive, condorcet_minimal_private_s3,
    condorcet_minimal_private_members, condorcet_minimal_private_complete,
    condorcet_minimal_private_core, condorcet_minimal_private_arc_witness,
    (by decide), condorcet_minimal_private_flow, ?_, ?_, ?_, ?_, condorcet_minimal_private_wellFounded⟩
  · exact condorcet_minimal_private_mass.1
  · exact condorcet_minimal_private_mass.2.1
  · exact condorcet_minimal_private_mass.2.2.1
  · exact condorcet_minimal_private_mass.2.2.2
