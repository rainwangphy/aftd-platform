import AFTD.Prelude
import AFTD.Kb.Tcs.RegularExpressionTypedParity
import AFTD.Kb.Tcs.RegularExpressionTypedParityLength

/-!
# regular_expression_exists_parity_normal_form

Topic: automata   Node: d7ee74034b6d

Provenance: formalization of a published result. Source: arXiv:2610.11717 (Every Regular Language Has a Bipartite Cactus Automaton), Lemma 3.1 (parity normal form).

For every regular expression r there are regular expressions r₀ and r₁, typed with parity 0 and 1 respectively, with L(r₀) = {w ∈ L(r) : |w| even} and L(r₁) = {w ∈ L(r) : |w| odd}; in particular every star in r₀ or r₁ is applied to an expression of parity 0.
-/

def regular_expression_parity_split {α : Type*} :
    RegularExpression α → RegularExpression α × RegularExpression α
  | .zero => (0, 0)
  | .epsilon => (1, 0)
  | .char a => (0, .char a)
  | .plus u v =>
    ((regular_expression_parity_split u).1 + (regular_expression_parity_split v).1,
      (regular_expression_parity_split u).2 + (regular_expression_parity_split v).2)
  | .comp u v =>
    ((regular_expression_parity_split u).1 * (regular_expression_parity_split v).1 +
        (regular_expression_parity_split u).2 * (regular_expression_parity_split v).2,
      (regular_expression_parity_split u).1 * (regular_expression_parity_split v).2 +
        (regular_expression_parity_split u).2 * (regular_expression_parity_split v).1)
  | .star u =>
    (RegularExpression.star (regular_expression_parity_split u).1 *
        RegularExpression.star ((regular_expression_parity_split u).2 *
          RegularExpression.star (regular_expression_parity_split u).1 *
          (regular_expression_parity_split u).2 *
          RegularExpression.star (regular_expression_parity_split u).1),
      RegularExpression.star (regular_expression_parity_split u).1 *
        (regular_expression_parity_split u).2 *
        RegularExpression.star (regular_expression_parity_split u).1 *
        RegularExpression.star ((regular_expression_parity_split u).2 *
          RegularExpression.star (regular_expression_parity_split u).1 *
          (regular_expression_parity_split u).2 *
          RegularExpression.star (regular_expression_parity_split u).1))

theorem regular_expression_parity_split_spec {α : Type*} (r : RegularExpression α) :
    regular_expression_typed_parity (regular_expression_parity_split r).1 0 ∧
      regular_expression_typed_parity (regular_expression_parity_split r).2 1 ∧
      (∀ w, w ∈ (regular_expression_parity_split r).1.matches' ↔
        w ∈ r.matches' ∧ w.length % 2 = 0) ∧
      (∀ w, w ∈ (regular_expression_parity_split r).2.matches' ↔
        w ∈ r.matches' ∧ w.length % 2 = 1) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  induction r with
  | zero =>
    refine ⟨trivial, trivial, fun w => ?_, fun w => ?_⟩ <;>
    · change w ∈ (0 : Language α) ↔ w ∈ (0 : Language α) ∧ _
      simp [Language.notMem_zero]
  | epsilon =>
    refine ⟨rfl, trivial, fun w => ?_, fun w => ?_⟩
    · change w ∈ (1 : Language α) ↔ w ∈ (1 : Language α) ∧ _
      rw [Language.mem_one]
      constructor
      · rintro rfl; simp
      · exact fun h => h.1
    · change w ∈ (0 : Language α) ↔ w ∈ (1 : Language α) ∧ _
      rw [Language.mem_one]
      simp only [Language.notMem_zero, false_iff, not_and]
      rintro rfl
      simp
  | char a =>
    refine ⟨trivial, rfl, fun w => ?_, fun w => ?_⟩
    · change w ∈ (0 : Language α) ↔ w ∈ ({[a]} : Language α) ∧ _
      simp only [Language.notMem_zero, false_iff, not_and]
      intro h
      replace h : w = [a] := h
      subst h
      simp
    · change w ∈ ({[a]} : Language α) ↔ w ∈ ({[a]} : Language α) ∧ _
      constructor
      · intro h
        refine ⟨h, ?_⟩
        replace h : w = [a] := h
        subst h
        simp
      · exact fun h => h.1
  | plus u v ihu ihv =>
    obtain ⟨tu0, tu1, mu0, mu1⟩ := ihu
    obtain ⟨tv0, tv1, mv0, mv1⟩ := ihv
    refine ⟨⟨tu0, tv0⟩, ⟨tu1, tv1⟩, fun w => ?_, fun w => ?_⟩
    · change w ∈ _ + _ ↔ w ∈ u.matches' + v.matches' ∧ _
      rw [Language.mem_add, Language.mem_add, mu0, mv0]
      tauto
    · change w ∈ _ + _ ↔ w ∈ u.matches' + v.matches' ∧ _
      rw [Language.mem_add, Language.mem_add, mu1, mv1]
      tauto
  | comp u v ihu ihv =>
    obtain ⟨tu0, tu1, mu0, mu1⟩ := ihu
    obtain ⟨tv0, tv1, mv0, mv1⟩ := ihv
    refine ⟨⟨⟨0, 0, by decide, tu0, tv0⟩, ⟨1, 1, h11, tu1, tv1⟩⟩,
      ⟨⟨0, 1, by decide, tu0, tv1⟩, ⟨1, 0, by decide, tu1, tv0⟩⟩, fun w => ?_, fun w => ?_⟩
    · change w ∈ _ * _ + _ * _ ↔ w ∈ u.matches' * v.matches' ∧ _
      simp only [Language.mem_add, Language.mem_mul, mu0, mu1, mv0, mv1]
      constructor
      · rintro (⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, rfl⟩ | ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, rfl⟩) <;>
        exact ⟨⟨a, ha, b, hb, rfl⟩, by simp [List.length_append]; omega⟩
      · rintro ⟨⟨a, ha, b, hb, rfl⟩, hw⟩
        rw [List.length_append] at hw
        rcases Nat.mod_two_eq_zero_or_one a.length with h | h
        · exact Or.inl ⟨a, ⟨ha, h⟩, b, ⟨hb, by omega⟩, rfl⟩
        · exact Or.inr ⟨a, ⟨ha, h⟩, b, ⟨hb, by omega⟩, rfl⟩
    · change w ∈ _ * _ + _ * _ ↔ w ∈ u.matches' * v.matches' ∧ _
      simp only [Language.mem_add, Language.mem_mul, mu0, mu1, mv0, mv1]
      constructor
      · rintro (⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, rfl⟩ | ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, rfl⟩) <;>
        exact ⟨⟨a, ha, b, hb, rfl⟩, by simp [List.length_append]; omega⟩
      · rintro ⟨⟨a, ha, b, hb, rfl⟩, hw⟩
        rw [List.length_append] at hw
        rcases Nat.mod_two_eq_zero_or_one a.length with h | h
        · exact Or.inl ⟨a, ⟨ha, h⟩, b, ⟨hb, by omega⟩, rfl⟩
        · exact Or.inr ⟨a, ⟨ha, h⟩, b, ⟨hb, by omega⟩, rfl⟩
  | star u ihu =>
    obtain ⟨tu0, tu1, mu0, mu1⟩ := ihu
    simp only [regular_expression_parity_split]
    set u0 := (regular_expression_parity_split u).1 with hu0
    set u1 := (regular_expression_parity_split u).2 with hu1
    have tc : regular_expression_typed_parity
        (u1 * RegularExpression.star u0 * u1 * RegularExpression.star u0) 0 :=
      ⟨0, 0, by decide, ⟨1, 1, h11, ⟨1, 0, by decide, tu1, ⟨rfl, tu0⟩⟩, tu1⟩, ⟨rfl, tu0⟩⟩
    have tA : regular_expression_typed_parity (RegularExpression.star u0 *
        RegularExpression.star (u1 * RegularExpression.star u0 * u1 *
          RegularExpression.star u0)) 0 :=
      ⟨0, 0, by decide, ⟨rfl, tu0⟩, ⟨rfl, tc⟩⟩
    have tB : regular_expression_typed_parity (RegularExpression.star u0 * u1 *
        RegularExpression.star u0 * RegularExpression.star (u1 * RegularExpression.star u0 * u1 *
          RegularExpression.star u0)) 1 :=
      ⟨1, 0, by decide, ⟨1, 0, by decide, ⟨0, 1, by decide, ⟨rfl, tu0⟩, tu1⟩, ⟨rfl, tu0⟩⟩,
        ⟨rfl, tc⟩⟩
    have pA := regular_expression_typed_parity_length _ 0 tA
    have pB := regular_expression_typed_parity_length _ 1 tB
    have toMod : ∀ (n : ℕ) (p : ZMod 2), (n : ZMod 2) = p → n % 2 = p.val := fun n p h => by
      rw [← h, ZMod.val_natCast]
    set U := u.matches' with hU
    set U0 := u0.matches' with hU0d
    set U1 := u1.matches' with hU1d
    set D := (KStar.kstar U0) with hDd
    set C := U1 * D * U1 * D with hCd
    have hU0 : U0 ≤ U := fun w hw => ((mu0 w).1 hw).1
    have hU1 : U1 ≤ U := fun w hw => ((mu1 w).1 hw).1
    have hUsplit : U ≤ U0 + U1 := by
      intro w hw
      refine (Language.mem_add U0 U1 w).2 ?_
      rcases Nat.mod_two_eq_zero_or_one w.length with h | h
      · exact Or.inl ((mu0 w).2 ⟨hw, h⟩)
      · exact Or.inr ((mu1 w).2 ⟨hw, h⟩)
    have hD : D ≤ (KStar.kstar U) := kstar_mono hU0
    have hU1s : U1 ≤ (KStar.kstar U) := hU1.trans le_kstar
    have hC : C ≤ (KStar.kstar U) := by
      calc C ≤ (KStar.kstar U) * (KStar.kstar U) * (KStar.kstar U) * (KStar.kstar U) := by rw [hCd]; gcongr
        _ = (KStar.kstar U) := by rw [kstar_mul_kstar, kstar_mul_kstar, kstar_mul_kstar]
    have hCs : (KStar.kstar C) ≤ (KStar.kstar U) := by
      calc (KStar.kstar C) ≤ KStar.kstar (KStar.kstar U) := kstar_mono hC
        _ = (KStar.kstar U) := kstar_idem U
    have hA : D * (KStar.kstar C) ≤ (KStar.kstar U) := by
      calc D * (KStar.kstar C) ≤ (KStar.kstar U) * (KStar.kstar U) := by gcongr
        _ = (KStar.kstar U) := kstar_mul_kstar U
    have hB : D * U1 * D * (KStar.kstar C) ≤ (KStar.kstar U) := by
      calc D * U1 * D * (KStar.kstar C) ≤ (KStar.kstar U) * (KStar.kstar U) * (KStar.kstar U) * (KStar.kstar U) := by gcongr
        _ = (KStar.kstar U) := by rw [kstar_mul_kstar, kstar_mul_kstar, kstar_mul_kstar]
    have h1D : (1 : Language α) ≤ D := one_le_kstar
    have h1C : (1 : Language α) ≤ (KStar.kstar C) := one_le_kstar
    have hAB : (KStar.kstar U) ≤ D * (KStar.kstar C) + D * U1 * D * (KStar.kstar C) := by
      apply kstar_le_of_mul_le_right
      · calc (1 : Language α) = 1 * 1 := (mul_one 1).symm
          _ ≤ D * (KStar.kstar C) := by gcongr
          _ ≤ _ := by rw [add_eq_sup]; exact le_sup_left
      · calc U * (D * (KStar.kstar C) + D * U1 * D * (KStar.kstar C)) ≤ (U0 + U1) * (D * (KStar.kstar C) + D * U1 * D * (KStar.kstar C)) := by
              gcongr
          _ = U0 * D * (KStar.kstar C) + U0 * D * U1 * D * (KStar.kstar C) + (U1 * D * (KStar.kstar C) + C * (KStar.kstar C)) := by
              rw [hCd]
              simp only [add_mul, mul_add, mul_assoc]
              abel
          _ ≤ D * (KStar.kstar C) + D * U1 * D * (KStar.kstar C) + (D * U1 * D * (KStar.kstar C) + D * (KStar.kstar C)) := by
              have e1 : U0 * D ≤ D := mul_kstar_le_kstar
              have e2 : U1 * D * (KStar.kstar C) ≤ D * U1 * D * (KStar.kstar C) := by
                calc U1 * D * (KStar.kstar C) = 1 * U1 * D * (KStar.kstar C) := by rw [one_mul]
                  _ ≤ D * U1 * D * (KStar.kstar C) := by gcongr
              have e3 : C * (KStar.kstar C) ≤ D * (KStar.kstar C) := by
                calc C * (KStar.kstar C) ≤ (KStar.kstar C) := mul_kstar_le_kstar
                  _ = 1 * (KStar.kstar C) := (one_mul _).symm
                  _ ≤ D * (KStar.kstar C) := by gcongr
              have e4 : U0 * D * U1 * D * (KStar.kstar C) ≤ D * U1 * D * (KStar.kstar C) := by gcongr
              have e5 : U0 * D * (KStar.kstar C) ≤ D * (KStar.kstar C) := by gcongr
              gcongr
          _ ≤ D * (KStar.kstar C) + D * U1 * D * (KStar.kstar C) := by
              simp only [add_eq_sup]
              exact sup_le le_rfl (sup_le le_sup_right le_sup_left)
    refine ⟨tA, tB, fun w => ?_, fun w => ?_⟩
    · change w ∈ D * (KStar.kstar C) ↔ w ∈ (KStar.kstar U) ∧ _
      constructor
      · intro hw
        exact ⟨hA hw, by simpa using toMod _ _ (pA w hw)⟩
      · rintro ⟨hw, hpar⟩
        rcases (Language.mem_add _ _ _).1 (hAB hw) with h | h
        · exact h
        · have := toMod _ _ (pB w h)
          rw [show (1 : ZMod 2).val = 1 from rfl] at this
          omega
    · change w ∈ D * U1 * D * (KStar.kstar C) ↔ w ∈ (KStar.kstar U) ∧ _
      constructor
      · intro hw
        exact ⟨hB hw, (toMod _ _ (pB w hw)).trans rfl⟩
      · rintro ⟨hw, hpar⟩
        rcases (Language.mem_add _ _ _).1 (hAB hw) with h | h
        · have := toMod _ _ (pA w h)
          simp at this
          omega
        · exact h

theorem regular_expression_exists_parity_normal_form {α : Type*} (r : RegularExpression α) :
    ∃ r₀ r₁ : RegularExpression α,
      regular_expression_typed_parity r₀ 0 ∧ regular_expression_typed_parity r₁ 1 ∧
      (∀ w, w ∈ r₀.matches' ↔ w ∈ r.matches' ∧ w.length % 2 = 0) ∧
      (∀ w, w ∈ r₁.matches' ↔ w ∈ r.matches' ∧ w.length % 2 = 1) :=
  ⟨_, _, regular_expression_parity_split_spec r⟩
