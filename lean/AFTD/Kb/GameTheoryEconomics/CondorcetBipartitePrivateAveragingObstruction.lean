import AFTD.Prelude

/-!
# condorcet_bipartite_private_averaging_obstruction

Topic: social_choice   Node: 2fcb613a525d

Provenance: helper lemma. IN-357 method diagnostic for OP-19. Search8939 and exact audit8940 test the complete-private-triple averaging construction under the additional bipartite-reciprocal-arc restriction. It strengthens the domain diagnostic of condorcet_complete_private_averaging_obstruction. It remains a failure of this particular weight rule, not an election counterexample or an obstruction to optimized policies. It asserts no global core minimality, no tournament condition, and no research advance.

There exist an irreflexive directed relation R on13 vertices with a common predecessor for every ordered triple, nonempty families F(a) of all private three-element sets at each root, natural per-triple occupations q, and an induced acyclic set U. Members of F(a) exclude a and have a as their unique common predecessor. Completeness is verified for every increasing triple a<b<c. With w(a)=card(F(a))*q(a), exact stationarity 3*w(b)=sum over a and J in F(a) containing b of q(a) holds. The total weight is94711649395739; U has weight48271809545321, strictly above half. There is a Boolean vertex coloring that assigns different colors to the endpoints of every pair of reciprocal arrows. Thus the reciprocal-arc graph is bipartite, but uniform averaging over all private triples still fails the acyclic half bound.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

def condorcet_bipartite_private_averaging_obstruction_pred : Fin 13 → ℕ := ![6424,6600,2515,8160,1930,7046,1834,3183,4282,4525,2607,362,3274]
def condorcet_bipartite_private_averaging_obstruction_relation (a b : Fin 13) : Prop :=
  (condorcet_bipartite_private_averaging_obstruction_pred b).testBit a.val = true
instance : DecidableRel condorcet_bipartite_private_averaging_obstruction_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_bipartite_private_averaging_obstruction_pred b).testBit a.val = true))
def condorcet_bipartite_private_averaging_obstruction_list : Fin 13 → List (Finset (Fin 13)) := ![[{2,7,9},{2,9,10}],[{2,4,7},{2,4,10},{2,6,7},{2,6,8},{2,6,10},{2,6,12},{2,7,8},{2,8,10},{2,8,11},{2,10,11},{4,5,7},{5,6,7},{5,6,8},{5,6,12},{5,7,8},{5,7,11},{5,8,10},{5,8,11},{5,10,11},{5,11,12}],[{5,7,9},{5,9,10}],[{0,4,7},{0,4,8},{0,4,10},{0,4,12},{0,6,7},{0,6,8},{0,6,10},{0,6,12},{0,7,8},{0,7,9},{0,7,11},{0,8,10},{0,8,11},{0,8,12},{0,9,10},{0,9,12},{0,10,11},{0,11,12},{1,4,7},{1,4,10},{1,6,7},{1,6,8},{1,6,10},{1,6,12},{1,7,8},{1,7,9},{1,8,10},{1,8,11},{1,9,10},{1,10,11},{4,7,9},{4,9,10},{6,9,12},{7,9,12},{9,10,12},{9,11,12}],[{0,2,8}],[{3,6,8},{3,7,8},{3,7,9},{3,8,10},{3,8,11},{3,9,10},{3,10,11}],[{3,11,12}],[{1,2,8},{2,3,8},{2,8,9},{2,9,12},{3,4,8},{3,8,12},{3,9,12},{5,9,12}],[{0,2,4},{0,2,6},{0,2,9},{0,2,11},{0,3,4},{0,3,6},{0,3,11},{0,4,5},{0,5,6},{0,5,11},{1,2,6},{1,3,6},{1,5,6},{1,5,11},{2,3,6},{2,6,9},{2,9,11},{3,4,11},{3,5,11},{5,6,9},{5,9,11}],[{3,4,10}],[{3,4,7},{3,6,12}],[{0,2,7},{0,2,10},{0,2,12},{0,3,7},{0,3,10},{0,3,12},{0,5,7},{0,5,10},{0,5,12},{1,2,10},{1,3,10},{1,5,7},{1,5,10},{2,3,10},{3,5,7},{3,10,12}],[{0,3,8},{0,5,8}]]
def condorcet_bipartite_private_averaging_obstruction_family (a : Fin 13) : Finset (Finset (Fin 13)) :=
  (condorcet_bipartite_private_averaging_obstruction_list a).toFinset
def condorcet_bipartite_private_averaging_obstruction_occupation : Fin 13 → ℕ := ![4299668706422,134392077744,4114538683596,374889478397,6651503342884,869741078867,4483864483247,883609578548,402160190852,9412306822863,4647660803425,268150145480,2981772533331]
def condorcet_bipartite_private_averaging_obstruction_weight (a : Fin 13) : ℕ :=
  (condorcet_bipartite_private_averaging_obstruction_family a).card * condorcet_bipartite_private_averaging_obstruction_occupation a
def condorcet_bipartite_private_averaging_obstruction_order : Fin 13 → ℕ := ![2,0,3,0,0,0,0,0,0,4,5,1,0]
def condorcet_bipartite_private_averaging_obstruction_set : Finset (Fin 13) := {8,11,0,2,9,10}
def condorcet_bipartite_private_averaging_obstruction_color : Fin 13 → Bool :=
  ![false,false,false,false,false,false,true,true,true,true,true,true,true]

theorem condorcet_bipartite_private_averaging_obstruction_irreflexive : ∀ a,
    ¬condorcet_bipartite_private_averaging_obstruction_relation a a := by decide

theorem condorcet_bipartite_private_averaging_obstruction_s3 : ∀ a b c : Fin 13,
    ∃ r, condorcet_bipartite_private_averaging_obstruction_relation r a ∧
      condorcet_bipartite_private_averaging_obstruction_relation r b ∧
      condorcet_bipartite_private_averaging_obstruction_relation r c := by decide

theorem condorcet_bipartite_private_averaging_obstruction_members : ∀ a,
    (condorcet_bipartite_private_averaging_obstruction_family a).Nonempty ∧
    ∀ J ∈ condorcet_bipartite_private_averaging_obstruction_family a,
      J.card = 3 ∧ a ∉ J ∧
      (∀ b ∈ J, condorcet_bipartite_private_averaging_obstruction_relation a b) ∧
      ∀ r, (∀ b ∈ J, condorcet_bipartite_private_averaging_obstruction_relation r b) → r = a := by
  have hnonempty : ∀ a, (condorcet_bipartite_private_averaging_obstruction_family a).Nonempty := by decide
  have hcheck : ∀ a, (condorcet_bipartite_private_averaging_obstruction_list a).all (fun J =>
      decide (J.card = 3 ∧ a ∉ J ∧
        (∀ b ∈ J, condorcet_bipartite_private_averaging_obstruction_relation a b) ∧
        ∀ r, (∀ b ∈ J, condorcet_bipartite_private_averaging_obstruction_relation r b) → r = a)) = true := by
    decide
  intro a
  refine ⟨hnonempty a, ?_⟩
  intro J hJ
  have hm : J ∈ condorcet_bipartite_private_averaging_obstruction_list a := by
    exact List.mem_toFinset.mp hJ
  exact of_decide_eq_true (List.all_eq_true.mp (hcheck a) J hm)

theorem condorcet_bipartite_private_averaging_obstruction_complete : ∀ r a b c : Fin 13,
    a < b → b < c →
    ({a,b,c} ∈ condorcet_bipartite_private_averaging_obstruction_family r ↔
      condorcet_bipartite_private_averaging_obstruction_relation r a ∧
      condorcet_bipartite_private_averaging_obstruction_relation r b ∧
      condorcet_bipartite_private_averaging_obstruction_relation r c ∧
      ∀ s, (condorcet_bipartite_private_averaging_obstruction_relation s a ∧
        condorcet_bipartite_private_averaging_obstruction_relation s b ∧
        condorcet_bipartite_private_averaging_obstruction_relation s c) → s = r) := by decide

theorem condorcet_bipartite_private_averaging_obstruction_flow : ∀ b : Fin 13,
    3 * condorcet_bipartite_private_averaging_obstruction_weight b =
      ∑ a : Fin 13, ∑ J ∈ condorcet_bipartite_private_averaging_obstruction_family a,
        if b ∈ J then condorcet_bipartite_private_averaging_obstruction_occupation a else 0 := by decide

theorem condorcet_bipartite_private_averaging_obstruction_mass :
    (∑ a : Fin 13, condorcet_bipartite_private_averaging_obstruction_weight a) = 94711649395739 ∧
    (∑ a ∈ condorcet_bipartite_private_averaging_obstruction_set, condorcet_bipartite_private_averaging_obstruction_weight a) = 48271809545321 ∧
    0 < (∑ a : Fin 13, condorcet_bipartite_private_averaging_obstruction_weight a) ∧
    (∑ a : Fin 13, condorcet_bipartite_private_averaging_obstruction_weight a) <
      2 * (∑ a ∈ condorcet_bipartite_private_averaging_obstruction_set, condorcet_bipartite_private_averaging_obstruction_weight a) := by decide

theorem condorcet_bipartite_private_averaging_obstruction_ordered : ∀ a b : Fin 13,
    a ∈ condorcet_bipartite_private_averaging_obstruction_set → b ∈ condorcet_bipartite_private_averaging_obstruction_set →
    condorcet_bipartite_private_averaging_obstruction_relation a b →
      condorcet_bipartite_private_averaging_obstruction_order a < condorcet_bipartite_private_averaging_obstruction_order b := by decide

theorem condorcet_bipartite_private_averaging_obstruction_wellFounded :
    WellFounded (fun a b : {a : Fin 13 // a ∈ condorcet_bipartite_private_averaging_obstruction_set} =>
      condorcet_bipartite_private_averaging_obstruction_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 13 // a ∈ condorcet_bipartite_private_averaging_obstruction_set} =>
    condorcet_bipartite_private_averaging_obstruction_order a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_bipartite_private_averaging_obstruction_ordered a.val b.val a.property b.property hab

theorem condorcet_bipartite_private_averaging_obstruction_coloring : ∀ a b,
    condorcet_bipartite_private_averaging_obstruction_relation a b →
    condorcet_bipartite_private_averaging_obstruction_relation b a →
    condorcet_bipartite_private_averaging_obstruction_color a ≠ condorcet_bipartite_private_averaging_obstruction_color b := by decide

theorem condorcet_bipartite_private_averaging_obstruction :
    ∃ (R : Fin 13 → Fin 13 → Prop)
      (F : Fin 13 → Finset (Finset (Fin 13))) (q : Fin 13 → ℕ)
      (U : Finset (Fin 13)),
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
      (∑ a, (F a).card * q a) = 94711649395739 ∧
      (∑ a ∈ U, (F a).card * q a) = 48271809545321 ∧
      0 < (∑ a, (F a).card * q a) ∧
      (∑ a, (F a).card * q a) < 2 * (∑ a ∈ U, (F a).card * q a) ∧
      WellFounded (fun a b : {a : Fin 13 // a ∈ U} => R a.val b.val) ∧
      (∃ color : Fin 13 → Bool, ∀ a b, R a b → R b a → color a ≠ color b) := by
  refine ⟨condorcet_bipartite_private_averaging_obstruction_relation,
    condorcet_bipartite_private_averaging_obstruction_family,
    condorcet_bipartite_private_averaging_obstruction_occupation,
    condorcet_bipartite_private_averaging_obstruction_set,
    condorcet_bipartite_private_averaging_obstruction_irreflexive,
    condorcet_bipartite_private_averaging_obstruction_s3,
    condorcet_bipartite_private_averaging_obstruction_members,
    condorcet_bipartite_private_averaging_obstruction_complete,
    condorcet_bipartite_private_averaging_obstruction_flow, ?_, ?_, ?_, ?_,
    condorcet_bipartite_private_averaging_obstruction_wellFounded, ?_⟩
  · exact condorcet_bipartite_private_averaging_obstruction_mass.1
  · exact condorcet_bipartite_private_averaging_obstruction_mass.2.1
  · exact condorcet_bipartite_private_averaging_obstruction_mass.2.2.1
  · exact condorcet_bipartite_private_averaging_obstruction_mass.2.2.2
  · exact ⟨condorcet_bipartite_private_averaging_obstruction_color,
      condorcet_bipartite_private_averaging_obstruction_coloring⟩
