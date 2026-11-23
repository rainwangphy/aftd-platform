import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialRankingSolution
import AFTD.Kb.GameTheoryEconomics.SatisfiesCon
import AFTD.Kb.GameTheoryEconomics.SatisfiesUcon
import AFTD.Kb.GameTheoryEconomics.SatisfiesLe
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.PowerProfile
import AFTD.Kb.GameTheoryEconomics.LexGe
import AFTD.Kb.GameTheoryEconomics.LexCel
import AFTD.Kb.GameTheoryEconomics.IsMergingSumPowerRelation
import AFTD.Kb.GameTheoryEconomics.SrsStrict
import AFTD.Kb.GameTheoryEconomics.PowerRelationCarrier
import AFTD.Kb.GameTheoryEconomics.PowerRelationRel
import AFTD.Kb.GameTheoryEconomics.IsMergingSumPowerProfile
import AFTD.Kb.GameTheoryEconomics.AppearanceVector

/-!
# impossibility_con_ucon_lex_cel_claim2

Topic: social_choice   Node: 156be9213e2e

Provenance: helper lemma. arXiv:2611.19021 Claim 2

If an SRS R satisfies consistency (satisfies_con), union consistency (satisfies_ucon), and Lex-cel extension (satisfies_le), and x ≠ y are individuals disjoint from a finite coalition S, and r₁, r₂ are power relations whose single equivalence classes are {insert x S} and {insert y S} respectively, then R ranks x and y indifferent at the profile {r₁, r₂} (both R.rel {r₁, r₂} x y and R.rel {r₁, r₂} y x hold).
-/

lemma impossibility_con_ucon_lex_cel_claim2_aux {X : Type*} [DecidableEq X]
    (R : SocialRankingSolution X)
    (hCON : satisfies_con R) (hUCON : satisfies_ucon R) (hLE : satisfies_le R)
    (x y : X) (hxy : x ≠ y) (S : Finset X) (hS : x ∉ S ∧ y ∉ S)
    (r₁ r₂ : PowerRelation X)
    (hr₁ : r₁.classes = [{insert x S}])
    (hr₂ : r₂.classes = [{insert y S}]) :
    ¬ srs_strict R {r₁, r₂} x y := by
  intro h_strict
  let C : Finset (Finset X) := {insert x S, insert y S}
  have hC_ne : ∀ c ∈ [C], c.Nonempty := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨insert x S, Finset.mem_insert_self _ _⟩
  have hC_disj : List.Pairwise Disjoint [C] := List.Pairwise.nil.cons (by simp)
  let r' : PowerRelation X := ⟨[C], hC_ne, hC_disj⟩
  have hr' : r'.classes = [{insert x S, insert y S}] := rfl
  have hne : insert x S ≠ insert y S := by
    intro h
    have : x ∈ insert x S := Finset.mem_insert_self x S
    rw [h] at this
    simp [Finset.mem_insert, hxy, hS.1] at this

  have h_merge1 : is_merging_sum_power_relation r' r₁ r₂ := by
    dsimp [is_merging_sum_power_relation]
    have c1 : power_relation_carrier r₁ = ({insert x S} : Set (Finset X)) := by
      rcases r₁ with ⟨cl, h1, h2⟩; dsimp at hr₁ ⊢; subst hr₁; dsimp [power_relation_carrier]; ext A; simp
    have c2 : power_relation_carrier r₂ = ({insert y S} : Set (Finset X)) := by
      rcases r₂ with ⟨cl, h1, h2⟩; dsimp at hr₂ ⊢; subst hr₂; dsimp [power_relation_carrier]; ext A; simp
    have c' : power_relation_carrier r' = ({insert x S, insert y S} : Set (Finset X)) := by
      rcases r' with ⟨cl, h1, h2⟩; dsimp at hr' ⊢; subst hr'; dsimp [power_relation_carrier]; ext A; simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [c1, c2]
      exact Set.disjoint_singleton_left.mpr (by simp [hne])
    · rw [c', c1, c2]
      ext A; simp [or_comm]
    · intro A hA B hB
      rw [c1] at hA hB
      simp only [Set.mem_singleton_iff] at hA hB
      subst hA hB
      have hA' : insert x S ∈ ({insert x S, insert y S} : Finset (Finset X)) := by simp
      have h1 : power_relation_rel r' (insert x S) (insert x S) := by
        rcases r' with ⟨cl, hne', hd'⟩; dsimp at hr' ⊢; subst hr'
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, hA', hA', le_rfl⟩
      have h2 : power_relation_rel r₁ (insert x S) (insert x S) := by
        rcases r₁ with ⟨cl, hne', hd'⟩; dsimp at hr₁ ⊢; subst hr₁
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, by simp, by simp, le_rfl⟩
      exact iff_of_true h1 h2
    · intro A hA B hB
      rw [c2] at hA hB
      simp only [Set.mem_singleton_iff] at hA hB
      subst hA hB
      have hA' : insert y S ∈ ({insert x S, insert y S} : Finset (Finset X)) := by simp
      have h1 : power_relation_rel r' (insert y S) (insert y S) := by
        rcases r' with ⟨cl, hne', hd'⟩; dsimp at hr' ⊢; subst hr'
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, hA', hA', le_rfl⟩
      have h2 : power_relation_rel r₂ (insert y S) (insert y S) := by
        rcases r₂ with ⟨cl, hne', hd'⟩; dsimp at hr₂ ⊢; subst hr₂
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, by simp, by simp, le_rfl⟩
      exact iff_of_true h1 h2

  have h_merge2 : is_merging_sum_power_relation r' r₂ r₁ := by
    dsimp [is_merging_sum_power_relation]
    have c1 : power_relation_carrier r₁ = ({insert x S} : Set (Finset X)) := by
      rcases r₁ with ⟨cl, h1, h2⟩; dsimp at hr₁ ⊢; subst hr₁; dsimp [power_relation_carrier]; ext A; simp
    have c2 : power_relation_carrier r₂ = ({insert y S} : Set (Finset X)) := by
      rcases r₂ with ⟨cl, h1, h2⟩; dsimp at hr₂ ⊢; subst hr₂; dsimp [power_relation_carrier]; ext A; simp
    have c' : power_relation_carrier r' = ({insert x S, insert y S} : Set (Finset X)) := by
      rcases r' with ⟨cl, h1, h2⟩; dsimp at hr' ⊢; subst hr'; dsimp [power_relation_carrier]; ext A; simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [c1, c2]
      exact Set.disjoint_singleton_right.mpr (by simp [hne])
    · rw [c', c1, c2]
      ext A; simp
    · intro A hA B hB
      rw [c2] at hA hB
      simp only [Set.mem_singleton_iff] at hA hB
      subst hA hB
      have hA' : insert y S ∈ ({insert x S, insert y S} : Finset (Finset X)) := by simp
      have h1 : power_relation_rel r' (insert y S) (insert y S) := by
        rcases r' with ⟨cl, hne', hd'⟩; dsimp at hr' ⊢; subst hr'
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, hA', hA', le_rfl⟩
      have h2 : power_relation_rel r₂ (insert y S) (insert y S) := by
        rcases r₂ with ⟨cl, hne', hd'⟩; dsimp at hr₂ ⊢; subst hr₂
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, by simp, by simp, le_rfl⟩
      exact iff_of_true h1 h2
    · intro A hA B hB
      rw [c1] at hA hB
      simp only [Set.mem_singleton_iff] at hA hB
      subst hA hB
      have hA' : insert x S ∈ ({insert x S, insert y S} : Finset (Finset X)) := by simp
      have h1 : power_relation_rel r' (insert x S) (insert x S) := by
        rcases r' with ⟨cl, hne', hd'⟩; dsimp at hr' ⊢; subst hr'
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, hA', hA', le_rfl⟩
      have h2 : power_relation_rel r₁ (insert x S) (insert x S) := by
        rcases r₁ with ⟨cl, hne', hd'⟩; dsimp at hr₁ ⊢; subst hr₁
        exact ⟨0, 0, Nat.zero_lt_one, Nat.zero_lt_one, by simp, by simp, le_rfl⟩
      exact iff_of_true h1 h2

  have h_prof : is_merging_sum_power_profile ({r', r'} : PowerProfile X) {r₁, r₂} {r₁, r₂} := by
    use [r', r'], [r₁, r₂], [r₂, r₁]
    refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
    · change ({r₁, r₂} : PowerProfile X) = r₂ ::ₘ r₁ ::ₘ 0
      exact Multiset.cons_swap r₁ r₂ 0
    · intro i h₁ h₂ h
      match i with
      | 0 => exact h_merge1
      | 1 => exact h_merge2
      | n + 2 =>
        have : (n + 2) < 2 := h
        omega

  have h_strict_pp : srs_strict R ({r', r'} : PowerProfile X) x y := by
    have hCON_app := hCON {r₁, r₂} {r₁, r₂} {r', r'} rfl h_prof x y
    exact hCON_app.2 h_strict h_strict.1

  have h_not_rel : ¬ R.rel {r', r'} y x := h_strict_pp.2

  have h_le_yx : lex_cel r' y x := by
    dsimp [lex_cel]
    have hx1 : x ∈ insert x S := Finset.mem_insert_self x S
    have hx2 : x ∉ insert y S := by simp [Finset.mem_insert, hxy, hS.1]
    have hy1 : y ∉ insert x S := by simp [Finset.mem_insert, Ne.symm hxy, hS.2]
    have hy2 : y ∈ insert y S := Finset.mem_insert_self y S
    have hx_set : {s ∈ ({insert x S, insert y S} : Finset (Finset X)) | x ∈ s} = {insert x S} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | rfl), hs⟩
        · rfl
        · contradiction
      · rintro rfl
        exact ⟨Or.inl rfl, hx1⟩
    have hy_set : {s ∈ ({insert x S, insert y S} : Finset (Finset X)) | y ∈ s} = {insert y S} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | rfl), hs⟩
        · contradiction
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, hy2⟩
    have h_av_x : appearance_vector r' x = [1] := by
      dsimp [appearance_vector]; rw [hr']; dsimp [List.map]; rw [hx_set]; simp
    have h_av_y : appearance_vector r' y = [1] := by
      dsimp [appearance_vector]; rw [hr']; dsimp [List.map]; rw [hy_set]; simp
    rw [h_av_y, h_av_x]
    exact Or.inr ⟨rfl, trivial⟩

  have h_rel_single : R.rel {r'} y x := (hLE r' y x).mpr h_le_yx

  have h_rel_sum : R.rel ({r'} + {r'}) y x :=
    (hUCON {r'} {r'} y x).1 h_rel_single h_rel_single

  have h_eq : ({r', r'} : PowerProfile X) = {r'} + {r'} := by
    change r' ::ₘ r' ::ₘ 0 = (r' ::ₘ 0) + (r' ::ₘ 0)
    rw [Multiset.cons_add, Multiset.zero_add]

  rw [h_eq] at h_not_rel
  exact h_not_rel h_rel_sum

/-- Step 1 of Theorem 3: under CON, UCON, and LE, an SRS ranks x and y indifferent on a profile of two singleton power relations. -/
theorem impossibility_con_ucon_lex_cel_claim2 {X : Type*} [DecidableEq X]
    (R : SocialRankingSolution X)
    (hCON : satisfies_con R) (hUCON : satisfies_ucon R) (hLE : satisfies_le R)
    (x y : X) (hxy : x ≠ y) (S : Finset X) (hS : x ∉ S ∧ y ∉ S)
    (r₁ r₂ : PowerRelation X)
    (hr₁ : r₁.classes = [{insert x S}])
    (hr₂ : r₂.classes = [{insert y S}]) :
    R.rel {r₁, r₂} x y ∧ R.rel {r₁, r₂} y x := by
  have h1 : ¬ srs_strict R {r₁, r₂} x y :=
    impossibility_con_ucon_lex_cel_claim2_aux R hCON hUCON hLE x y hxy S hS r₁ r₂ hr₁ hr₂
  have h_swap : ({r₁, r₂} : PowerProfile X) = {r₂, r₁} := by
    change r₁ ::ₘ r₂ ::ₘ 0 = r₂ ::ₘ r₁ ::ₘ 0
    exact Multiset.cons_swap r₁ r₂ 0
  have h2' : ¬ srs_strict R {r₂, r₁} y x :=
    impossibility_con_ucon_lex_cel_claim2_aux R hCON hUCON hLE y x (Ne.symm hxy) S ⟨hS.2, hS.1⟩ r₂ r₁ hr₂ hr₁
  have h2 : ¬ srs_strict R {r₁, r₂} y x := by
    rw [h_swap]
    exact h2'
  cases R.complete {r₁, r₂} x y with
  | inl hxy_rel =>
    by_cases hyx_rel : R.rel {r₁, r₂} y x
    · exact ⟨hxy_rel, hyx_rel⟩
    · exfalso
      exact h1 ⟨hxy_rel, hyx_rel⟩
  | inr hyx_rel =>
    by_cases hxy_rel : R.rel {r₁, r₂} x y
    · exact ⟨hxy_rel, hyx_rel⟩
    · exfalso
      exact h2 ⟨hyx_rel, hxy_rel⟩
