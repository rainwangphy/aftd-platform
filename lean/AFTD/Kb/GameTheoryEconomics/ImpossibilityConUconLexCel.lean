import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialRankingSolution
import AFTD.Kb.GameTheoryEconomics.SatisfiesCon
import AFTD.Kb.GameTheoryEconomics.SatisfiesUcon
import AFTD.Kb.GameTheoryEconomics.SatisfiesLe
import AFTD.Kb.GameTheoryEconomics.ImpossibilityConUconLexCelClaim2
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.LexGe
import AFTD.Kb.GameTheoryEconomics.LexCel
import AFTD.Kb.GameTheoryEconomics.IsMergingSumPowerProfile
import AFTD.Kb.GameTheoryEconomics.PowerProfile
import AFTD.Kb.GameTheoryEconomics.SrsStrict
import AFTD.Kb.GameTheoryEconomics.PowerRelationCarrier
import AFTD.Kb.GameTheoryEconomics.PowerRelationRel
import AFTD.Kb.GameTheoryEconomics.AppearanceVector
import AFTD.Kb.GameTheoryEconomics.IsMergingSumPowerRelation

/-!
# impossibility_con_ucon_lex_cel

Topic: social_choice   Node: 5a361ebc4d44

Provenance: formalization of a published result. Source: arXiv:2611.19021 Theorem 3

For any countably infinite type of individuals X with decidable equality, no social ranking solution R on X simultaneously satisfies consistency (satisfies_con R), union consistency (satisfies_ucon R), and Lex-cel extension (satisfies_le R).
-/

lemma impossibility_con_ucon_lex_cel_pr_rel_refl {X : Type*} (r : PowerRelation X) (S : Finset X)
    (hS : S ∈ power_relation_carrier r) : power_relation_rel r S S := by
  rcases hS with ⟨c, hc, hSc⟩
  rw [List.mem_iff_getElem] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact ⟨i, i, hi, hi, hSc, hSc, le_rfl⟩

lemma impossibility_con_ucon_lex_cel_carrier_singleton {X : Type*} (r : PowerRelation X) (S : Finset X)
    (hr : r.classes = [{S}]) : power_relation_carrier r = {S} := by
  ext T
  simp [power_relation_carrier, hr]

lemma impossibility_con_ucon_lex_cel_carrier_two {X : Type*} (r : PowerRelation X) (S₁ S₂ : Finset X)
    (hr : r.classes = [{S₁}, {S₂}]) : power_relation_carrier r = {S₁, S₂} := by
  ext T
  simp [power_relation_carrier, hr]

lemma impossibility_con_ucon_lex_cel_carrier_one_two {X : Type*} [DecidableEq X] (r : PowerRelation X) (S₁ S₂ : Finset X)
    (hr : r.classes = [{S₁, S₂}]) : power_relation_carrier r = {S₁, S₂} := by
  ext T
  simp [power_relation_carrier, hr]

lemma impossibility_con_ucon_lex_cel_ms_of_singletons {X : Type*} (r r₁ r₂ : PowerRelation X) (S₁ S₂ : Finset X)
    (hS : S₁ ≠ S₂)
    (hr₁ : power_relation_carrier r₁ = {S₁})
    (hr₂ : power_relation_carrier r₂ = {S₂})
    (hr : power_relation_carrier r = {S₁, S₂}) :
    is_merging_sum_power_relation r r₁ r₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr₁, hr₂]
    exact Set.disjoint_singleton_left.mpr hS
  · rw [hr, hr₁, hr₂]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  · intro A hA B hB
    rw [hr₁] at hA hB
    simp only [Set.mem_singleton_iff] at hA hB
    rw [hA, hB]
    have hrS₁ : S₁ ∈ power_relation_carrier r := by rw [hr]; simp
    have hr₁S₁ : S₁ ∈ power_relation_carrier r₁ := by rw [hr₁]; simp
    exact iff_of_true (impossibility_con_ucon_lex_cel_pr_rel_refl r S₁ hrS₁)
      (impossibility_con_ucon_lex_cel_pr_rel_refl r₁ S₁ hr₁S₁)
  · intro A hA B hB
    rw [hr₂] at hA hB
    simp only [Set.mem_singleton_iff] at hA hB
    rw [hA, hB]
    have hrS₂ : S₂ ∈ power_relation_carrier r := by rw [hr]; simp
    have hr₂S₂ : S₂ ∈ power_relation_carrier r₂ := by rw [hr₂]; simp
    exact iff_of_true (impossibility_con_ucon_lex_cel_pr_rel_refl r S₂ hrS₂)
      (impossibility_con_ucon_lex_cel_pr_rel_refl r₂ S₂ hr₂S₂)

/-- Impossibility of reconciling consistency, union consistency, and Lex-cel extension: no social ranking solution satisfies CON, UCON, and LE simultaneously. -/
theorem impossibility_con_ucon_lex_cel (X : Type*) [DecidableEq X] [Countable X] [Infinite X] :
  ¬ ∃ (R : SocialRankingSolution X), satisfies_con R ∧ satisfies_ucon R ∧ satisfies_le R := by
  rintro ⟨R, hCON, hUCON, hLE⟩
  have h_univ : (Set.univ : Set X).Infinite := Set.infinite_univ
  obtain ⟨x, -⟩ := h_univ.nonempty
  have h_univ1 : (Set.univ \ {x} : Set X).Infinite := Set.Infinite.sdiff h_univ (Set.finite_singleton x)
  obtain ⟨y, hy⟩ := h_univ1.nonempty
  have hyx : y ≠ x := by aesop
  have h_univ2 : (Set.univ \ {x, y} : Set X).Infinite := Set.Infinite.sdiff h_univ (Set.toFinite {x, y})
  obtain ⟨z, hz⟩ := h_univ2.nonempty
  have hzx : z ≠ x := by aesop
  have hzy : z ≠ y := by aesop
  have hxy : x ≠ y := hyx.symm
  have hxz : x ≠ z := hzx.symm
  have hyz : y ≠ z := hzy.symm

  let S_x : Finset X := {x}
  let S_y : Finset X := {y}
  let S_yz : Finset X := {y, z}
  let S_xz : Finset X := {x, z}

  have h_Sx_ne_Syz : S_x ≠ S_yz := by
    intro h
    have hc : S_x.card = S_yz.card := by rw [h]
    rw [Finset.card_singleton, Finset.card_pair hyz] at hc
    omega

  have h_Sy_ne_Sxz : S_y ≠ S_xz := by
    intro h
    have hc : S_y.card = S_xz.card := by rw [h]
    rw [Finset.card_singleton, Finset.card_pair hxz] at hc
    omega

  let r₁ : PowerRelation X := {
    classes := [{S_x}]
    classes_nonempty := by simp [Finset.singleton_nonempty]
    classes_disjoint := by simp
  }

  let r₂ : PowerRelation X := {
    classes := [{S_y}]
    classes_nonempty := by simp [Finset.singleton_nonempty]
    classes_disjoint := by simp
  }

  let r₃ : PowerRelation X := {
    classes := [{S_xz}]
    classes_nonempty := by simp [Finset.singleton_nonempty]
    classes_disjoint := by simp
  }

  let r₄ : PowerRelation X := {
    classes := [{S_yz}]
    classes_nonempty := by simp [Finset.singleton_nonempty]
    classes_disjoint := by simp
  }

  let P₁ : PowerRelation X := {
    classes := [{S_x}, {S_yz}]
    classes_nonempty := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact Finset.singleton_nonempty _
    classes_disjoint := by
      rw [List.pairwise_cons]
      refine ⟨?_, by simp⟩
      intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      rw [Finset.disjoint_singleton_left, Finset.mem_singleton]
      exact h_Sx_ne_Syz
  }

  let P₂ : PowerRelation X := {
    classes := [{S_y, S_xz}]
    classes_nonempty := by
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨S_y, Finset.mem_insert_self S_y {S_xz}⟩
    classes_disjoint := by simp
  }

  have hr₁_c : power_relation_carrier r₁ = {S_x} :=
    impossibility_con_ucon_lex_cel_carrier_singleton r₁ S_x rfl
  have hr₂_c : power_relation_carrier r₂ = {S_y} :=
    impossibility_con_ucon_lex_cel_carrier_singleton r₂ S_y rfl
  have hr₃_c : power_relation_carrier r₃ = {S_xz} :=
    impossibility_con_ucon_lex_cel_carrier_singleton r₃ S_xz rfl
  have hr₄_c : power_relation_carrier r₄ = {S_yz} :=
    impossibility_con_ucon_lex_cel_carrier_singleton r₄ S_yz rfl
  have hP₁_c : power_relation_carrier P₁ = {S_x, S_yz} :=
    impossibility_con_ucon_lex_cel_carrier_two P₁ S_x S_yz rfl
  have hP₂_c : power_relation_carrier P₂ = {S_y, S_xz} :=
    impossibility_con_ucon_lex_cel_carrier_one_two P₂ S_y S_xz rfl

  have h_ms1 : is_merging_sum_power_relation P₁ r₁ r₄ :=
    impossibility_con_ucon_lex_cel_ms_of_singletons P₁ r₁ r₄ S_x S_yz h_Sx_ne_Syz hr₁_c hr₄_c hP₁_c

  have h_ms2 : is_merging_sum_power_relation P₂ r₂ r₃ :=
    impossibility_con_ucon_lex_cel_ms_of_singletons P₂ r₂ r₃ S_y S_xz h_Sy_ne_Sxz hr₂_c hr₃_c hP₂_c

  have h_ms_prof : is_merging_sum_power_profile ({P₁, P₂} : PowerProfile X) {r₁, r₂} {r₄, r₃} := by
    refine ⟨[P₁, P₂], [r₁, r₂], [r₄, r₃], rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro (_ | _ | n) h1 h2 h
    · exact h_ms1
    · exact h_ms2
    · simp at h1

  have h_c2_1 : R.rel {r₁, r₂} y x := by
    have h_empty : (x ∉ (∅ : Finset X)) ∧ (y ∉ (∅ : Finset X)) := by simp
    have hr1_eq : r₁.classes = [{insert x ∅}] := by simp [r₁, S_x]
    have hr2_eq : r₂.classes = [{insert y ∅}] := by simp [r₂, S_y]
    have h := impossibility_con_ucon_lex_cel_claim2 R hCON hUCON hLE x y hxy ∅ h_empty r₁ r₂ hr1_eq hr2_eq
    exact h.2

  have h_c2_2 : R.rel {r₄, r₃} y x := by
    have hz_not : (x ∉ ({z} : Finset X)) ∧ (y ∉ ({z} : Finset X)) := by
      simp [hxz, hyz]
    have hr3_eq : r₃.classes = [{insert x {z}}] := by rfl
    have hr4_eq : r₄.classes = [{insert y {z}}] := by rfl
    have h := impossibility_con_ucon_lex_cel_claim2 R hCON hUCON hLE x y hxy {z} hz_not r₃ r₄ hr3_eq hr4_eq
    have h_swap : ({r₄, r₃} : PowerProfile X) = {r₃, r₄} := by
      change r₄ ::ₘ r₃ ::ₘ 0 = r₃ ::ₘ r₄ ::ₘ 0
      exact Multiset.cons_swap r₄ r₃ 0
    rw [h_swap]
    exact h.2

  have h_con_yx : R.rel {P₁, P₂} y x := by
    have h_cards : Multiset.card ({r₁, r₂} : PowerProfile X) = Multiset.card ({r₄, r₃} : PowerProfile X) := rfl
    exact (hCON {r₁, r₂} {r₄, r₃} {P₁, P₂} h_cards h_ms_prof y x).1 h_c2_1 h_c2_2

  have h_P1_av_x : appearance_vector P₁ x = [1, 0] := by
    have h1 : ({S ∈ ({S_x} : Finset (Finset X)) | x ∈ S}) = {S_x} := by
      rw [Finset.filter_true_of_mem]
      simp [S_x]
    have h2 : ({S ∈ ({S_yz} : Finset (Finset X)) | x ∈ S}) = ∅ := by
      rw [Finset.filter_false_of_mem]
      simp [S_yz, hxy, hxz]
    change [{S ∈ ({S_x} : Finset (Finset X)) | x ∈ S}.card, {S ∈ ({S_yz} : Finset (Finset X)) | x ∈ S}.card] = [1, 0]
    rw [h1, h2]
    simp

  have h_P1_av_y : appearance_vector P₁ y = [0, 1] := by
    have h1 : ({S ∈ ({S_x} : Finset (Finset X)) | y ∈ S}) = ∅ := by
      rw [Finset.filter_false_of_mem]
      simp [S_x, hxy.symm]
    have h2 : ({S ∈ ({S_yz} : Finset (Finset X)) | y ∈ S}) = {S_yz} := by
      rw [Finset.filter_true_of_mem]
      simp [S_yz]
    change [{S ∈ ({S_x} : Finset (Finset X)) | y ∈ S}.card, {S ∈ ({S_yz} : Finset (Finset X)) | y ∈ S}.card] = [0, 1]
    rw [h1, h2]
    simp

  have h_P1_lex_xy : lex_cel P₁ x y := by
    dsimp [lex_cel]
    rw [h_P1_av_x, h_P1_av_y]
    dsimp [lex_ge]
    left
    omega

  have h_P1_not_lex_yx : ¬ lex_cel P₁ y x := by
    dsimp [lex_cel]
    rw [h_P1_av_x, h_P1_av_y]
    dsimp [lex_ge]
    intro h
    rcases h with h | ⟨h1, h2⟩ <;> omega

  have h_P1_strict : srs_strict R {P₁} x y := by
    dsimp [srs_strict]
    constructor
    · rw [hLE P₁ x y]
      exact h_P1_lex_xy
    · rw [hLE P₁ y x]
      exact h_P1_not_lex_yx

  have h_P2_av_x : appearance_vector P₂ x = [1] := by
    have h : ({S ∈ ({S_y, S_xz} : Finset (Finset X)) | x ∈ S}) = {S_xz} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, S_y, S_xz]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · simp at hx
          exact (hxy hx).elim
        · rfl
      · rintro rfl
        simp
    change [{S ∈ ({S_y, S_xz} : Finset (Finset X)) | x ∈ S}.card] = [1]
    rw [h]
    simp

  have h_P2_av_y : appearance_vector P₂ y = [1] := by
    have h : ({S ∈ ({S_y, S_xz} : Finset (Finset X)) | y ∈ S}) = {S_y} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, S_y, S_xz]
      constructor
      · rintro ⟨rfl | rfl, hy⟩
        · rfl
        · simp at hy
          rcases hy with rfl | rfl
          · exact (hxy.symm rfl).elim
          · exact (hyz rfl).elim
      · rintro rfl
        simp
    change [{S ∈ ({S_y, S_xz} : Finset (Finset X)) | y ∈ S}.card] = [1]
    rw [h]
    simp

  have h_P2_rel_xy : R.rel {P₂} x y := by
    rw [hLE P₂ x y]
    dsimp [lex_cel]
    rw [h_P2_av_x, h_P2_av_y]
    dsimp [lex_ge]
    right
    exact ⟨rfl, trivial⟩

  have h_ucon_strict : srs_strict R ({P₁, P₂} : PowerProfile X) x y := by
    have h_sum : ({P₁, P₂} : PowerProfile X) = {P₁} + {P₂} := rfl
    rw [h_sum]
    exact (hUCON {P₁} {P₂} x y).2 h_P1_strict h_P2_rel_xy

  exact h_ucon_strict.2 h_con_yx
