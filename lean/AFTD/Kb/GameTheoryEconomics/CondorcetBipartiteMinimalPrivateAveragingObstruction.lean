import AFTD.Prelude

/-!
# condorcet_bipartite_minimal_private_averaging_obstruction

Topic: social_choice   Node: 773040028e5c

Provenance: helper lemma. IN-362 finite method diagnostic for OP-19. Strengthens the old bipartite reciprocal-arc example by GLOBAL minimum core and arc minimality. Exact data audited computationally; NOT yet Lean proved. No election counterexample or research advance.

There is an irreflexive15-vertex S3 relation whose only induced S3 subset is the whole graph, every arrow lies in a private triple, and the reciprocal arrows are bipartite. The complete private families admit strictly positive integer occupations with stationary flow3w(b)=sum incoming occupations. Total65016484420889054890 and an induced acyclic set of weight32949241318203599358 violate the half bound. Thus even the bipartite reciprocal-arc restriction combined with global vertex and arc minimality does not repair uniform complete-private averaging.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

def condorcet_bipartite_minimal_private_pred : Fin 15 → ℕ := ![16082,16012,9857,24421,30348,16022,14242,523,18619,8303,2463,12299,10041,1035,523]
def condorcet_bipartite_minimal_private_relation (a b : Fin 15) : Prop :=
  (condorcet_bipartite_minimal_private_pred b).testBit a.val = true
instance : DecidableRel condorcet_bipartite_minimal_private_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_bipartite_minimal_private_pred b).testBit a.val = true))
def condorcet_bipartite_minimal_private_list : Fin 15 → List (Finset (Fin 15)) := ![[{2,3,8},{2,3,9},{2,3,10},{2,3,11},{2,7,8},{2,7,9},{2,7,10},{2,7,11},{2,7,13},{2,8,9},{2,8,11},{2,8,12},{2,8,13},{2,8,14},{2,9,10},{2,9,13},{2,9,14},{2,10,11},{2,10,12},{2,10,13},{2,10,14},{2,11,13},{2,11,14},{2,13,14},{3,7,8},{3,7,9},{3,7,10},{3,7,11},{3,7,13},{3,8,11},{3,8,13},{3,8,14},{3,9,11},{3,9,13},{3,9,14},{3,10,11},{3,10,13},{3,10,14},{3,11,12},{3,11,13},{3,11,14},{3,13,14}],[{0,7,8},{0,7,9},{0,7,10},{0,7,11},{0,7,13},{0,8,9},{0,8,11},{0,8,13},{0,8,14},{0,9,10},{0,9,13},{0,9,14},{0,10,11},{0,10,13},{0,10,14},{0,11,13},{0,11,14},{0,13,14},{5,7,8},{5,7,9},{5,7,10},{5,7,11},{5,7,13},{5,8,9},{5,8,11},{5,8,13},{5,8,14},{5,9,13},{5,9,14},{5,10,11},{5,10,13},{5,10,14},{5,11,13},{5,11,14},{5,13,14},{6,7,8},{6,7,9},{6,7,10},{6,7,11},{6,7,13},{6,8,11},{6,8,13},{6,8,14},{6,9,10},{6,9,13},{6,9,14},{6,10,11},{6,10,13},{6,10,14},{6,11,13},{6,11,14},{6,13,14}],[{1,3,9},{3,4,9},{3,4,10},{3,5,9}],[{1,7,8},{1,7,9},{1,7,10},{1,7,11},{1,7,13},{1,8,9},{1,8,11},{1,8,12},{1,8,13},{1,8,14},{1,9,13},{1,9,14},{1,10,11},{1,10,12},{1,10,13},{1,10,14},{1,11,13},{1,11,14},{1,13,14},{4,7,8},{4,7,9},{4,7,10},{4,7,11},{4,7,13},{4,8,9},{4,8,11},{4,8,12},{4,8,13},{4,8,14},{4,9,13},{4,9,14},{4,10,11},{4,10,12},{4,10,13},{4,10,14},{4,11,13},{4,11,14},{4,13,14}],[{0,8,12},{0,10,12},{5,8,12},{5,10,12}],[{3,6,8},{3,6,9},{6,8,12}],[{0,3,9}],[{0,2,8},{0,2,10},{0,4,8},{0,4,10},{1,2,8},{1,2,10},{1,6,8},{1,6,10},{2,4,8},{2,4,10},{2,5,8},{2,5,10},{2,6,8},{2,6,10},{4,5,8},{4,6,8},{4,6,10}],[{3,6,10},{6,10,12}],[{0,1,7},{0,1,14},{0,2,7},{0,2,14},{0,3,7},{0,3,14},{0,4,7},{0,4,14},{0,7,12},{0,12,14},{1,2,7},{1,2,14},{1,3,7},{1,3,14},{1,5,7},{1,5,14},{1,6,7},{1,6,14},{2,4,7},{2,4,14},{2,5,7},{2,5,14},{2,6,7},{2,6,14},{3,4,7},{3,4,14},{3,5,7},{3,5,14},{3,6,7},{3,6,14},{4,5,7},{4,5,14},{4,6,7},{4,6,14},{5,7,12},{5,12,14},{6,7,12},{6,12,14}],[{0,1,13},{0,2,13},{0,3,13},{0,4,13},{0,12,13},{1,2,13},{1,3,13},{1,5,13},{1,6,13},{2,4,13},{2,5,13},{2,6,13},{3,4,13},{3,5,13},{3,6,13},{4,5,13},{4,6,13},{5,12,13},{6,12,13}],[{0,3,8},{0,3,10},{1,3,8},{3,5,8}],[{0,3,11},{1,3,11},{3,4,11},{3,5,11},{3,6,11}],[{0,1,9},{0,2,9},{0,2,11},{0,4,9},{0,9,12},{0,11,12},{1,2,9},{1,2,11},{1,6,9},{2,4,9},{2,4,11},{2,5,9},{2,5,11},{2,6,9},{2,6,11},{4,6,9},{5,9,12},{5,11,12},{6,11,12}],[{3,4,8}]]
def condorcet_bipartite_minimal_private_family (a : Fin 15) : Finset (Finset (Fin 15)) :=
  (condorcet_bipartite_minimal_private_list a).toFinset
def condorcet_bipartite_minimal_private_occupation : Fin 15 → ℕ := ![122302088000489630,70610140282895734,734812011212854860,245816903459202084,1138701283410615507,1075808512214415316,4986221101208269346,140159060107615556,2670517002872160086,126724739297265274,265882714522224420,888759696569514400,810094822257257864,188424245588257680,2382704021829464452]
def condorcet_bipartite_minimal_private_weight (a : Fin 15) : ℕ :=
  (condorcet_bipartite_minimal_private_family a).card * condorcet_bipartite_minimal_private_occupation a
def condorcet_bipartite_minimal_private_order : Fin 15 → ℕ := ![0,0,2,0,5,6,8,0,7,0,0,3,0,1,4]
def condorcet_bipartite_minimal_private_set : Finset (Fin 15) := {7,13,2,11,14,4,5,8,6}

theorem condorcet_bipartite_minimal_private_irreflexive : ∀ a,
    ¬condorcet_bipartite_minimal_private_relation a a := by decide +kernel

theorem condorcet_bipartite_minimal_private_s3 : ∀ a b c : Fin 15,
    ∃ r, condorcet_bipartite_minimal_private_relation r a ∧
      condorcet_bipartite_minimal_private_relation r b ∧
      condorcet_bipartite_minimal_private_relation r c := by decide +kernel

theorem condorcet_bipartite_minimal_private_members : ∀ a,
    (condorcet_bipartite_minimal_private_family a).Nonempty ∧
    ∀ J ∈ condorcet_bipartite_minimal_private_family a,
      J.card = 3 ∧ a ∉ J ∧
      (∀ b ∈ J, condorcet_bipartite_minimal_private_relation a b) ∧
      ∀ r, (∀ b ∈ J, condorcet_bipartite_minimal_private_relation r b) → r = a := by
  have hnonempty : ∀ a, (condorcet_bipartite_minimal_private_family a).Nonempty := by decide +kernel
  have hcheck : ∀ a, (condorcet_bipartite_minimal_private_list a).all (fun J =>
      decide (J.card = 3 ∧ a ∉ J ∧
        (∀ b ∈ J, condorcet_bipartite_minimal_private_relation a b) ∧
        ∀ r, (∀ b ∈ J, condorcet_bipartite_minimal_private_relation r b) → r = a)) = true := by
    decide +kernel
  intro a
  refine ⟨hnonempty a, ?_⟩
  intro J hJ
  have hm : J ∈ condorcet_bipartite_minimal_private_list a := by
    exact List.mem_toFinset.mp hJ
  exact of_decide_eq_true (List.all_eq_true.mp (hcheck a) J hm)

theorem condorcet_bipartite_minimal_private_complete_forward (r a b c : Fin 15)
    (hJ : {a, b, c} ∈ condorcet_bipartite_minimal_private_family r) :
    condorcet_bipartite_minimal_private_relation r a ∧
    condorcet_bipartite_minimal_private_relation r b ∧
    condorcet_bipartite_minimal_private_relation r c ∧
    ∀ s, (condorcet_bipartite_minimal_private_relation s a ∧
      condorcet_bipartite_minimal_private_relation s b ∧
      condorcet_bipartite_minimal_private_relation s c) → s = r := by
  have hmem := (condorcet_bipartite_minimal_private_members r).2 {a, b, c} hJ
  refine ⟨hmem.2.2.1 a (by simp), hmem.2.2.1 b (by simp), hmem.2.2.1 c (by simp), ?_⟩
  intro s ⟨hsa, hsb, hsc⟩
  apply hmem.2.2.2 s
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hsa
  · exact hsb
  · exact hsc

theorem condorcet_bipartite_minimal_private_complete_backward : ∀ a b c : Fin 15, a < b → b < c → ∀ r,
    (condorcet_bipartite_minimal_private_relation r a ∧
     condorcet_bipartite_minimal_private_relation r b ∧
     condorcet_bipartite_minimal_private_relation r c ∧
     ∀ s, (condorcet_bipartite_minimal_private_relation s a ∧
           condorcet_bipartite_minimal_private_relation s b ∧
           condorcet_bipartite_minimal_private_relation s c) → s = r) →
    {a,b,c} ∈ condorcet_bipartite_minimal_private_family r := by decide +kernel

theorem condorcet_bipartite_minimal_private_complete : ∀ r a b c : Fin 15,
    a < b → b < c →
    ({a,b,c} ∈ condorcet_bipartite_minimal_private_family r ↔
      condorcet_bipartite_minimal_private_relation r a ∧
      condorcet_bipartite_minimal_private_relation r b ∧
      condorcet_bipartite_minimal_private_relation r c ∧
      ∀ s, (condorcet_bipartite_minimal_private_relation s a ∧
        condorcet_bipartite_minimal_private_relation s b ∧
        condorcet_bipartite_minimal_private_relation s c) → s = r) := by
  intro r a b c hab hbc
  constructor
  · exact condorcet_bipartite_minimal_private_complete_forward r a b c
  · exact condorcet_bipartite_minimal_private_complete_backward a b c hab hbc r

theorem condorcet_bipartite_minimal_private_flow : ∀ b : Fin 15,
    3 * condorcet_bipartite_minimal_private_weight b =
      ∑ a : Fin 15, ∑ J ∈ condorcet_bipartite_minimal_private_family a,
        if b ∈ J then condorcet_bipartite_minimal_private_occupation a else 0 := by decide +kernel

theorem condorcet_bipartite_minimal_private_mass :
    (∑ a : Fin 15, condorcet_bipartite_minimal_private_weight a) = 65016484420889054890 ∧
    (∑ a ∈ condorcet_bipartite_minimal_private_set, condorcet_bipartite_minimal_private_weight a) = 32949241318203599358 ∧
    0 < (∑ a : Fin 15, condorcet_bipartite_minimal_private_weight a) ∧
    (∑ a : Fin 15, condorcet_bipartite_minimal_private_weight a) <
      2 * (∑ a ∈ condorcet_bipartite_minimal_private_set, condorcet_bipartite_minimal_private_weight a) := by decide +kernel

theorem condorcet_bipartite_minimal_private_ordered : ∀ a b : Fin 15,
    a ∈ condorcet_bipartite_minimal_private_set → b ∈ condorcet_bipartite_minimal_private_set →
    condorcet_bipartite_minimal_private_relation a b →
      condorcet_bipartite_minimal_private_order a < condorcet_bipartite_minimal_private_order b := by decide +kernel

theorem condorcet_bipartite_minimal_private_wellFounded :
    WellFounded (fun a b : {a : Fin 15 // a ∈ condorcet_bipartite_minimal_private_set} =>
      condorcet_bipartite_minimal_private_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 15 // a ∈ condorcet_bipartite_minimal_private_set} =>
    condorcet_bipartite_minimal_private_order a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_bipartite_minimal_private_ordered a.val b.val a.property b.property hab


theorem condorcet_bipartite_minimal_private_arc_witness : ∀ a b : Fin 15,
    condorcet_bipartite_minimal_private_relation a b →
    ∃ J ∈ condorcet_bipartite_minimal_private_family a, b ∈ J := by decide +kernel

/-- Clauses `(j, d)`: `j` is the mask of a set `J` of at most three vertices and `d` adds to
it every vertex outside `J` that precedes all of `J`. A vertex mask `m` with
`m &&& d = j` contains `J` and no such predecessor, so it violates the closure hypothesis at `J`. -/
def condorcet_bipartite_minimal_private_cert : List (ℕ × ℕ) :=
  [(129, 643), (130, 650), (260, 389), (136, 649), (515, 8707), (641, 643), (644, 645), (8195, 9219), (1029, 1157), (536, 540), (8224, 9250), (1090, 1218), (128, 651), (16393, 16905), (8706, 8714), (1028, 1157), (1040, 1180), (16960, 16962), (8200, 9225), (6176, 14368), (522, 526), (514, 8718), (8193, 9219), (16386, 16906), (131, 643), (16392, 16905), (640, 651), (5, 9861), (513, 8771), (9248, 9250), (320, 482), (516, 8709), (544, 8742), (16384, 16907), (1033, 3081), (2056, 6153), (2057, 6153), (8192, 9227), (4, 9861), (8194, 9226), (5121, 5137), (9224, 9225), (16385, 16899), (16, 30364), (576, 8802), (280, 16664), (512, 8815), (4098, 13834), (520, 621), (4106, 5642), (1088, 1474), (288, 2482), (66, 14018), (1026, 3214), (9216, 9227), (3074, 3082), (4112, 13848), (2080, 14370), (4097, 13841), (1032, 3341), (40, 7724), (9217, 9219), (4120, 5656), (517, 8709), (6152, 6153), (2, 16014), (64, 14306), (2050, 14346), (264, 18729), (9, 7753), (521, 585), (6144, 14345), (8, 24429), (32, 16054), (256, 18875), (1024, 3487), (2048, 14347), (2049, 14339), (4128, 13872), (1041, 1169), (1096, 1352), (1025, 3219), (1, 16083), (4096, 14137), (4104, 5929), (266, 2314), (0, 32767), (328, 360)]

/-- The vertex set encoded by the bits of `m`. -/
def condorcet_bipartite_minimal_private_decode (m : ℕ) : Finset (Fin 15) :=
  Finset.univ.filter (fun a : Fin 15 => m.testBit a.val = true)

/-- Every mask but the full one meets some clause. -/
def condorcet_bipartite_minimal_private_check (m : ℕ) : Bool :=
  m.beq 32767 || condorcet_bipartite_minimal_private_cert.any (fun e => (m &&& e.2).beq e.1)

theorem condorcet_bipartite_minimal_private_check_all :
    ∀ h < 128, ∀ l < 256, condorcet_bipartite_minimal_private_check (h * 256 + l) = true := by
  decide +kernel

theorem condorcet_bipartite_minimal_private_cert_sound :
    ∀ e ∈ condorcet_bipartite_minimal_private_cert,
      (condorcet_bipartite_minimal_private_decode e.1).card ≤ 3 ∧
      ∀ a : Fin 15, a ∉ condorcet_bipartite_minimal_private_decode e.1 →
        (∀ b ∈ condorcet_bipartite_minimal_private_decode e.1,
          condorcet_bipartite_minimal_private_relation a b) → e.2.testBit a.val = true := by
  decide +kernel

theorem condorcet_bipartite_minimal_private_decode_surj :
    ∀ B : Finset (Fin 15), ∃ m < 32768, condorcet_bipartite_minimal_private_decode m = B := by
  intro B
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by ext a; simp [condorcet_bipartite_minimal_private_decode]⟩
  | insert a s _ ih =>
    obtain ⟨m, hm, hms⟩ := ih
    refine ⟨m ||| 2 ^ a.val, ?_, ?_⟩
    · have ha : 2 ^ a.val < 2 ^ 15 := Nat.pow_lt_pow_right (by norm_num) a.isLt
      exact Nat.or_lt_two_pow (by simpa using hm) ha
    · rw [← hms]
      ext x
      simp only [condorcet_bipartite_minimal_private_decode, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert, Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq, Fin.ext_iff]
      tauto

theorem condorcet_bipartite_minimal_private_core : ∀ B : Finset (Fin 15),
    (∀ J : Finset (Fin 15), J ⊆ B → J.card ≤ 3 →
      ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, condorcet_bipartite_minimal_private_relation a b) →
    B = Finset.univ := by
  intro B hB
  obtain ⟨m, hm, rfl⟩ := condorcet_bipartite_minimal_private_decode_surj B
  have hc : condorcet_bipartite_minimal_private_check m = true := by
    have h := condorcet_bipartite_minimal_private_check_all (m / 256) (by omega) (m % 256) (by omega)
    rwa [show m / 256 * 256 + m % 256 = m by omega] at h
  simp only [condorcet_bipartite_minimal_private_check, Bool.or_eq_true, Nat.beq_eq,
    List.any_eq_true] at hc
  rcases hc with hfull | ⟨e, he, hok⟩
  · subst hfull
    ext a
    simp only [condorcet_bipartite_minimal_private_decode, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    revert a
    decide +kernel
  · exfalso
    obtain ⟨hcard, hpred⟩ := condorcet_bipartite_minimal_private_cert_sound e he
    have hJ : condorcet_bipartite_minimal_private_decode e.1 ⊆
        condorcet_bipartite_minimal_private_decode m := by
      intro a ha
      simp only [condorcet_bipartite_minimal_private_decode, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha ⊢
      rw [← hok, Nat.testBit_land] at ha
      exact (Bool.and_eq_true _ _).mp ha |>.1
    obtain ⟨a, haB, haJ, hR⟩ := hB _ hJ hcard
    have h1 := hpred a haJ hR
    have h2 : m.testBit a.val = true := by
      simpa [condorcet_bipartite_minimal_private_decode] using haB
    apply haJ
    simp only [condorcet_bipartite_minimal_private_decode, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [← hok, Nat.testBit_land, h1, h2]
    rfl

def condorcet_bipartite_minimal_private_color : Fin 15 → Bool :=
  ![false,false,false,false,false,false,false,true,true,true,true,true,true,true,true]
theorem condorcet_bipartite_minimal_private_coloring : ∀ a b : Fin 15,
  condorcet_bipartite_minimal_private_relation a b →
  condorcet_bipartite_minimal_private_relation b a →
  condorcet_bipartite_minimal_private_color a ≠ condorcet_bipartite_minimal_private_color b := by decide +kernel

theorem condorcet_bipartite_minimal_private_averaging_obstruction :
    ∃ (R : Fin 15 → Fin 15 → Prop)
      (F : Fin 15 → Finset (Finset (Fin 15))) (q : Fin 15 → ℕ)
      (U : Finset (Fin 15)),
      (∀ a, ¬ R a a) ∧
      (∀ a b c, ∃ r, R r a ∧ R r b ∧ R r c) ∧
      (∀ a, (F a).Nonempty ∧ ∀ J ∈ F a,
        J.card = 3 ∧ a ∉ J ∧ (∀ b ∈ J, R a b) ∧
        ∀ r, (∀ b ∈ J, R r b) → r = a) ∧
      (∀ r a b c, a < b → b < c →
        ({a,b,c} ∈ F r ↔ R r a ∧ R r b ∧ R r c ∧
          ∀ s, (R s a ∧ R s b ∧ R s c) → s = r)) ∧
      (∀ B : Finset (Fin 15),
        (∀ J : Finset (Fin 15), J ⊆ B → J.card ≤ 3 →
          ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, R a b) → B = univ) ∧
      (∀ a b, R a b → ∃ J ∈ F a, b ∈ J) ∧
      (∃ color : Fin 15 → Bool, ∀ a b, R a b → R b a → color a ≠ color b) ∧
      (∀ a, 0 < q a) ∧
      (∀ b, 3 * ((F b).card * q b) =
        ∑ a, ∑ J ∈ F a, if b ∈ J then q a else 0) ∧
      (∑ a, (F a).card * q a) = 65016484420889054890 ∧
      (∑ a ∈ U, (F a).card * q a) = 32949241318203599358 ∧
      0 < (∑ a, (F a).card * q a) ∧
      (∑ a, (F a).card * q a) < 2 * (∑ a ∈ U, (F a).card * q a) ∧
      WellFounded (fun a b : {a : Fin 15 // a ∈ U} => R a.val b.val) := by
  refine ⟨condorcet_bipartite_minimal_private_relation, condorcet_bipartite_minimal_private_family,
    condorcet_bipartite_minimal_private_occupation, condorcet_bipartite_minimal_private_set,
    condorcet_bipartite_minimal_private_irreflexive, condorcet_bipartite_minimal_private_s3,
    condorcet_bipartite_minimal_private_members, condorcet_bipartite_minimal_private_complete,
    condorcet_bipartite_minimal_private_core, condorcet_bipartite_minimal_private_arc_witness,
    ⟨condorcet_bipartite_minimal_private_color, condorcet_bipartite_minimal_private_coloring⟩,
    (by decide +kernel), condorcet_bipartite_minimal_private_flow, ?_, ?_, ?_, ?_, condorcet_bipartite_minimal_private_wellFounded⟩
  · exact condorcet_bipartite_minimal_private_mass.1
  · exact condorcet_bipartite_minimal_private_mass.2.1
  · exact condorcet_bipartite_minimal_private_mass.2.2.1
  · exact condorcet_bipartite_minimal_private_mass.2.2.2
