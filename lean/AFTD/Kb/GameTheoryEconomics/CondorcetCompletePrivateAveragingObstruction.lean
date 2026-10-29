import AFTD.Prelude

/-!
# condorcet_complete_private_averaging_obstruction

Topic: social_choice   Node: 43c987ad065d

Provenance: helper lemma. IN-357 method diagnostic for OP-19, search8929 and exact integer audit8932. It concerns the complete-private-triple averaging rule, which is distinct from arbitrary chosen private triples and from the older all-committee eviction rule. This is no election counterexample, no obstruction to optimized vertex weights, and no research advance. Reciprocal arrows are allowed; no oriented/tournament conclusion is asserted.

There exist an irreflexive directed relation R on16 vertices with a common predecessor for every ordered triple, a nonempty finite family F(a) of private three-element sets at every root a, natural occupations q, and an induced acyclic subset U. Every member of F(a) excludes a and has a as its unique common predecessor. Completeness is checked for every increasing triple a<b<c: its set belongs to F(r) if and only if r is its unique common predecessor, so all private three-element sets are present. With w(a)=card(F(a))*q(a), the exact identity 3*w(b)=sum over a and J in F(a) containing b of q(a) holds. These weights therefore obey stationarity for uniform averaging over all private triples at each root, then uniformly over their three vertices. Total weight is2876598259756430344, while U has weight1447017722375641758, strictly above half. This is a counterexample to this particular averaging construction.
-/

open Finset
open scoped BigOperators

def condorcet_complete_private_pred : Fin 16 → ℕ := ![38834,43481,10976,31008,36456,20296,19120,17272,15584,3376,2988,26173,28102,3184,3937,31314]
def condorcet_complete_private_relation (a b : Fin 16) : Prop :=
  (condorcet_complete_private_pred b).testBit a.val = true
instance : DecidableRel condorcet_complete_private_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_complete_private_pred b).testBit a.val = true))
def condorcet_complete_private_list : Fin 16 → List (Finset (Fin 16)) := ![[{1,11,14}],[{0,12,15}],[{10,11,12}],[{1,4,11},{1,5,11},{1,10,11}],[{0,1,11},{0,1,13},{0,1,15},{0,9,15},{0,13,15},{1,6,7},{1,6,11},{1,9,11},{1,11,13},{7,9,15},{9,11,15},{11,13,15}],[{0,2,3},{0,2,9},{0,2,13},{0,3,4},{0,3,6},{0,3,11},{0,3,13},{0,7,8},{0,10,13},{2,3,7},{2,7,9},{2,9,11},{2,11,13},{3,4,7},{3,4,11},{3,7,8},{3,7,13},{3,9,11},{3,10,11},{3,11,13},{3,11,14},{4,7,9},{6,7,8},{6,8,11},{7,8,9},{7,8,10},{7,8,11},{7,10,13},{8,10,11},{9,10,11},{10,11,13}],[{1,2,7},{1,7,8},{2,7,12},{4,7,12},{5,7,8},{5,7,13},{7,8,12},{7,8,15},{7,12,13}],[{0,1,2},{0,1,8},{0,2,12},{0,6,12}],[{0,1,3},{0,1,5},{0,1,14},{0,3,5},{0,3,12},{0,7,12},{1,3,7},{5,7,9},{7,9,12},{7,10,12}],[{0,2,5},{0,2,15},{0,4,15},{0,5,6},{0,5,15},{0,10,15},{0,14,15},{2,5,11},{4,11,15},{7,10,15},{10,11,15},{11,14,15}],[{0,4,12},{0,5,8},{0,5,13},{0,11,12},{0,12,13},{4,11,12},{5,8,11},{5,9,11},{5,11,13},{9,11,12},{11,12,13},{11,12,14}],[{1,2,9},{1,3,4},{1,3,6},{1,3,13},{1,4,6},{1,4,9},{1,5,6},{1,6,14},{1,8,9},{1,10,13},{1,10,15},{2,3,5},{2,5,9},{2,9,12},{2,9,15},{3,4,5},{3,4,12},{3,4,15},{3,5,8},{3,5,13},{3,9,15},{3,10,15},{3,12,13},{3,13,15},{3,14,15},{4,6,12},{4,9,15},{4,10,12},{5,6,8},{5,6,9},{5,6,13},{5,8,10},{5,9,15},{5,10,13},{6,8,15},{6,9,12},{6,12,13},{6,12,14},{8,9,15},{8,10,15},{9,10,15},{9,12,15},{9,14,15},{10,12,13},{10,12,15},{10,13,15}],[{0,3,15},{0,8,15}],[{1,2,11},{1,3,11},{1,8,11},{1,11,12},{2,11,12},{8,11,15}],[{3,5,11},{3,7,15},{6,7,12},{6,11,12},{7,11,12}],[{0,1,4}]]
def condorcet_complete_private_family (a : Fin 16) : Finset (Finset (Fin 16)) :=
  (condorcet_complete_private_list a).toFinset
def condorcet_complete_private_occupation : Fin 16 → ℕ := ![446845983201704302,410053001074363439,53104951062296765,44040360322123860,13435306768598744,2847193144423017,8111824930189959,24287979033766593,10039264993826346,5930674449492833,6211566117902783,7155402591528509,138138318586479658,10507928470947514,33761797781530410,331446981381001084]
def condorcet_complete_private_weight (a : Fin 16) : ℕ :=
  (condorcet_complete_private_family a).card * condorcet_complete_private_occupation a
def condorcet_complete_private_order : Fin 16 → ℕ := ![7,0,3,5,0,0,1,0,0,0,0,0,4,2,0,6]
def condorcet_complete_private_set : Finset (Fin 16) := {9,6,13,2,12,3,15,0}

theorem condorcet_complete_private_irreflexive : ∀ a,
    ¬condorcet_complete_private_relation a a := by decide

theorem condorcet_complete_private_s3 : ∀ a b c : Fin 16,
    ∃ r, condorcet_complete_private_relation r a ∧
      condorcet_complete_private_relation r b ∧
      condorcet_complete_private_relation r c := by decide

theorem condorcet_complete_private_members : ∀ a,
    (condorcet_complete_private_family a).Nonempty ∧
    ∀ J ∈ condorcet_complete_private_family a,
      J.card = 3 ∧ a ∉ J ∧
      (∀ b ∈ J, condorcet_complete_private_relation a b) ∧
      ∀ r, (∀ b ∈ J, condorcet_complete_private_relation r b) → r = a := by
  have hnonempty : ∀ a, (condorcet_complete_private_family a).Nonempty := by decide
  have hcheck : ∀ a, (condorcet_complete_private_list a).all (fun J =>
      decide (J.card = 3 ∧ a ∉ J ∧
        (∀ b ∈ J, condorcet_complete_private_relation a b) ∧
        ∀ r, (∀ b ∈ J, condorcet_complete_private_relation r b) → r = a)) = true := by
    decide
  intro a
  refine ⟨hnonempty a, ?_⟩
  intro J hJ
  have hm : J ∈ condorcet_complete_private_list a := by
    exact List.mem_toFinset.mp hJ
  exact of_decide_eq_true (List.all_eq_true.mp (hcheck a) J hm)

theorem condorcet_complete_private_complete_forward (r a b c : Fin 16)
    (hJ : {a, b, c} ∈ condorcet_complete_private_family r) :
    condorcet_complete_private_relation r a ∧
    condorcet_complete_private_relation r b ∧
    condorcet_complete_private_relation r c ∧
    ∀ s, (condorcet_complete_private_relation s a ∧
      condorcet_complete_private_relation s b ∧
      condorcet_complete_private_relation s c) → s = r := by
  have hmem := (condorcet_complete_private_members r).2 {a, b, c} hJ
  refine ⟨hmem.2.2.1 a (by simp), hmem.2.2.1 b (by simp), hmem.2.2.1 c (by simp), ?_⟩
  intro s ⟨hsa, hsb, hsc⟩
  apply hmem.2.2.2 s
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hsa
  · exact hsb
  · exact hsc

theorem condorcet_complete_private_complete_backward : ∀ a b c : Fin 16, a < b → b < c → ∀ r,
    (condorcet_complete_private_relation r a ∧
     condorcet_complete_private_relation r b ∧
     condorcet_complete_private_relation r c ∧
     ∀ s, (condorcet_complete_private_relation s a ∧
           condorcet_complete_private_relation s b ∧
           condorcet_complete_private_relation s c) → s = r) →
    {a,b,c} ∈ condorcet_complete_private_family r := by decide

theorem condorcet_complete_private_complete : ∀ r a b c : Fin 16,
    a < b → b < c →
    ({a,b,c} ∈ condorcet_complete_private_family r ↔
      condorcet_complete_private_relation r a ∧
      condorcet_complete_private_relation r b ∧
      condorcet_complete_private_relation r c ∧
      ∀ s, (condorcet_complete_private_relation s a ∧
        condorcet_complete_private_relation s b ∧
        condorcet_complete_private_relation s c) → s = r) := by
  intro r a b c hab hbc
  constructor
  · exact condorcet_complete_private_complete_forward r a b c
  · exact condorcet_complete_private_complete_backward a b c hab hbc r

theorem condorcet_complete_private_flow : ∀ b : Fin 16,
    3 * condorcet_complete_private_weight b =
      ∑ a : Fin 16, ∑ J ∈ condorcet_complete_private_family a,
        if b ∈ J then condorcet_complete_private_occupation a else 0 := by decide

theorem condorcet_complete_private_mass :
    (∑ a : Fin 16, condorcet_complete_private_weight a) = 2876598259756430344 ∧
    (∑ a ∈ condorcet_complete_private_set, condorcet_complete_private_weight a) = 1447017722375641758 ∧
    0 < (∑ a : Fin 16, condorcet_complete_private_weight a) ∧
    (∑ a : Fin 16, condorcet_complete_private_weight a) <
      2 * (∑ a ∈ condorcet_complete_private_set, condorcet_complete_private_weight a) := by decide

theorem condorcet_complete_private_ordered : ∀ a b : Fin 16,
    a ∈ condorcet_complete_private_set → b ∈ condorcet_complete_private_set →
    condorcet_complete_private_relation a b →
      condorcet_complete_private_order a < condorcet_complete_private_order b := by decide

theorem condorcet_complete_private_wellFounded :
    WellFounded (fun a b : {a : Fin 16 // a ∈ condorcet_complete_private_set} =>
      condorcet_complete_private_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 16 // a ∈ condorcet_complete_private_set} =>
    condorcet_complete_private_order a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_complete_private_ordered a.val b.val a.property b.property hab

theorem condorcet_complete_private_averaging_obstruction :
    ∃ (R : Fin 16 → Fin 16 → Prop)
      (F : Fin 16 → Finset (Finset (Fin 16))) (q : Fin 16 → ℕ)
      (U : Finset (Fin 16)),
      (∀ a, ¬ R a a) ∧
      (∀ a b c, ∃ r, R r a ∧ R r b ∧ R r c) ∧
      (∀ a, (F a).Nonempty ∧ ∀ J ∈ F a,
        J.card = 3 ∧ a ∉ J ∧ (∀ b ∈ J, R a b) ∧
        ∀ r, (∀ b ∈ J, R r b) → r = a) ∧
      (∀ r a b c, a < b → b < c →
        ({a,b,c} ∈ F r ↔ R r a ∧ R r b ∧ R r c ∧
          ∀ s, (R s a ∧ R s b ∧ R s c) → s = r)) ∧
      (∀ b, 3 * ((F b).card * q b) =
        ∑ a, ∑ J ∈ F a, if b ∈ J then q a else 0) ∧
      (∑ a, (F a).card * q a) = 2876598259756430344 ∧
      (∑ a ∈ U, (F a).card * q a) = 1447017722375641758 ∧
      0 < (∑ a, (F a).card * q a) ∧
      (∑ a, (F a).card * q a) < 2 * (∑ a ∈ U, (F a).card * q a) ∧
      WellFounded (fun a b : {a : Fin 16 // a ∈ U} => R a.val b.val) := by
  refine ⟨condorcet_complete_private_relation, condorcet_complete_private_family,
    condorcet_complete_private_occupation, condorcet_complete_private_set,
    condorcet_complete_private_irreflexive, condorcet_complete_private_s3,
    condorcet_complete_private_members, condorcet_complete_private_complete,
    condorcet_complete_private_flow, ?_, ?_, ?_, ?_, condorcet_complete_private_wellFounded⟩
  · exact condorcet_complete_private_mass.1
  · exact condorcet_complete_private_mass.2.1
  · exact condorcet_complete_private_mass.2.2.1
  · exact condorcet_complete_private_mass.2.2.2
