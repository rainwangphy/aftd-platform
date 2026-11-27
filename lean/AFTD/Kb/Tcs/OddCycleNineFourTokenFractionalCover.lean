import AFTD.Prelude
import AFTD.Kb.Tcs.C

/-!
# odd_cycle_nine_four_token_fractional_cover

Topic: graphs   Node: e67deb281d16

Provenance: original. Related work: arXiv:2611.22830

There exists a function assigning a nonnegative rational weight to each vertex set C of a directed 9-cycle in the 4-token graph of Z/9Z (where an arc replaces some x in S with x+1 when x+1 is unoccupied) such that for every 4-subset S of Z/9Z, the sum of weights of cycles containing S equals 1.
-/

theorem odd_cycle_nine_four_token_fractional_cover_shift_set_card (s : Finset (ZMod 9)) (k : ZMod 9) (h : s.card = 4) :
    (s.image (· + k)).card = 4 := by
  rw [Finset.card_image_of_injective s (fun a b hab => add_right_cancel hab), h]

def odd_cycle_nine_four_token_fractional_cover_shift_sub (s : { s : Finset (ZMod 9) // s.card = 4 }) (k : ZMod 9) :
    { s : Finset (ZMod 9) // s.card = 4 } :=
  ⟨s.val.image (· + k), odd_cycle_nine_four_token_fractional_cover_shift_set_card s.val k s.property⟩

def odd_cycle_nine_four_token_fractional_cover_base_c : Fin 12 → Fin 9 → { s : Finset (ZMod 9) // s.card = 4 }
  | 0, 0 => ⟨{0, 2, 3, 7}, by decide⟩
  | 0, 1 => ⟨{0, 2, 4, 7}, by decide⟩
  | 0, 2 => ⟨{1, 2, 4, 7}, by decide⟩
  | 0, 3 => ⟨{1, 2, 4, 8}, by decide⟩
  | 0, 4 => ⟨{1, 2, 5, 8}, by decide⟩
  | 0, 5 => ⟨{1, 3, 5, 8}, by decide⟩
  | 0, 6 => ⟨{2, 3, 5, 8}, by decide⟩
  | 0, 7 => ⟨{2, 3, 6, 8}, by decide⟩
  | 0, 8 => ⟨{2, 3, 7, 8}, by decide⟩
  | 1, 0 => ⟨{0, 2, 3, 7}, by decide⟩
  | 1, 1 => ⟨{0, 2, 4, 7}, by decide⟩
  | 1, 2 => ⟨{0, 3, 4, 7}, by decide⟩
  | 1, 3 => ⟨{1, 3, 4, 7}, by decide⟩
  | 1, 4 => ⟨{1, 3, 5, 7}, by decide⟩
  | 1, 5 => ⟨{1, 3, 5, 8}, by decide⟩
  | 1, 6 => ⟨{1, 3, 6, 8}, by decide⟩
  | 1, 7 => ⟨{2, 3, 6, 8}, by decide⟩
  | 1, 8 => ⟨{2, 3, 7, 8}, by decide⟩
  | 2, 0 => ⟨{0, 2, 4, 7}, by decide⟩
  | 2, 1 => ⟨{0, 2, 5, 7}, by decide⟩
  | 2, 2 => ⟨{0, 3, 5, 7}, by decide⟩
  | 2, 3 => ⟨{1, 3, 5, 7}, by decide⟩
  | 2, 4 => ⟨{1, 4, 5, 7}, by decide⟩
  | 2, 5 => ⟨{1, 4, 6, 7}, by decide⟩
  | 2, 6 => ⟨{1, 4, 6, 8}, by decide⟩
  | 2, 7 => ⟨{1, 4, 7, 8}, by decide⟩
  | 2, 8 => ⟨{2, 4, 7, 8}, by decide⟩
  | 3, 0 => ⟨{0, 2, 3, 5}, by decide⟩
  | 3, 1 => ⟨{0, 2, 4, 5}, by decide⟩
  | 3, 2 => ⟨{1, 2, 4, 5}, by decide⟩
  | 3, 3 => ⟨{1, 3, 4, 5}, by decide⟩
  | 3, 4 => ⟨{2, 3, 4, 5}, by decide⟩
  | 3, 5 => ⟨{2, 3, 4, 6}, by decide⟩
  | 3, 6 => ⟨{2, 3, 4, 7}, by decide⟩
  | 3, 7 => ⟨{2, 3, 4, 8}, by decide⟩
  | 3, 8 => ⟨{2, 3, 5, 8}, by decide⟩
  | 4, 0 => ⟨{0, 2, 4, 6}, by decide⟩
  | 4, 1 => ⟨{0, 2, 4, 7}, by decide⟩
  | 4, 2 => ⟨{1, 2, 4, 7}, by decide⟩
  | 4, 3 => ⟨{1, 3, 4, 7}, by decide⟩
  | 4, 4 => ⟨{2, 3, 4, 7}, by decide⟩
  | 4, 5 => ⟨{2, 3, 5, 7}, by decide⟩
  | 4, 6 => ⟨{2, 3, 6, 7}, by decide⟩
  | 4, 7 => ⟨{2, 4, 6, 7}, by decide⟩
  | 4, 8 => ⟨{2, 4, 6, 8}, by decide⟩
  | 5, 0 => ⟨{0, 1, 4, 5}, by decide⟩
  | 5, 1 => ⟨{0, 2, 4, 5}, by decide⟩
  | 5, 2 => ⟨{0, 3, 4, 5}, by decide⟩
  | 5, 3 => ⟨{0, 3, 4, 6}, by decide⟩
  | 5, 4 => ⟨{0, 3, 4, 7}, by decide⟩
  | 5, 5 => ⟨{0, 3, 4, 8}, by decide⟩
  | 5, 6 => ⟨{0, 3, 5, 8}, by decide⟩
  | 5, 7 => ⟨{0, 4, 5, 8}, by decide⟩
  | 5, 8 => ⟨{1, 4, 5, 8}, by decide⟩
  | 6, 0 => ⟨{0, 3, 4, 6}, by decide⟩
  | 6, 1 => ⟨{0, 3, 5, 6}, by decide⟩
  | 6, 2 => ⟨{1, 3, 5, 6}, by decide⟩
  | 6, 3 => ⟨{1, 4, 5, 6}, by decide⟩
  | 6, 4 => ⟨{2, 4, 5, 6}, by decide⟩
  | 6, 5 => ⟨{3, 4, 5, 6}, by decide⟩
  | 6, 6 => ⟨{3, 4, 5, 7}, by decide⟩
  | 6, 7 => ⟨{3, 4, 5, 8}, by decide⟩
  | 6, 8 => ⟨{3, 4, 6, 8}, by decide⟩
  | 7, 0 => ⟨{0, 3, 4, 5}, by decide⟩
  | 7, 1 => ⟨{0, 3, 4, 6}, by decide⟩
  | 7, 2 => ⟨{0, 3, 5, 6}, by decide⟩
  | 7, 3 => ⟨{1, 3, 5, 6}, by decide⟩
  | 7, 4 => ⟨{2, 3, 5, 6}, by decide⟩
  | 7, 5 => ⟨{2, 4, 5, 6}, by decide⟩
  | 7, 6 => ⟨{3, 4, 5, 6}, by decide⟩
  | 7, 7 => ⟨{3, 4, 5, 7}, by decide⟩
  | 7, 8 => ⟨{3, 4, 5, 8}, by decide⟩
  | 8, 0 => ⟨{0, 1, 4, 5}, by decide⟩
  | 8, 1 => ⟨{0, 2, 4, 5}, by decide⟩
  | 8, 2 => ⟨{1, 2, 4, 5}, by decide⟩
  | 8, 3 => ⟨{1, 2, 4, 6}, by decide⟩
  | 8, 4 => ⟨{1, 2, 5, 6}, by decide⟩
  | 8, 5 => ⟨{1, 3, 5, 6}, by decide⟩
  | 8, 6 => ⟨{1, 3, 5, 7}, by decide⟩
  | 8, 7 => ⟨{1, 3, 5, 8}, by decide⟩
  | 8, 8 => ⟨{1, 4, 5, 8}, by decide⟩
  | 9, 0 => ⟨{0, 3, 4, 6}, by decide⟩
  | 9, 1 => ⟨{1, 3, 4, 6}, by decide⟩
  | 9, 2 => ⟨{1, 3, 5, 6}, by decide⟩
  | 9, 3 => ⟨{2, 3, 5, 6}, by decide⟩
  | 9, 4 => ⟨{2, 4, 5, 6}, by decide⟩
  | 9, 5 => ⟨{3, 4, 5, 6}, by decide⟩
  | 9, 6 => ⟨{3, 4, 5, 7}, by decide⟩
  | 9, 7 => ⟨{3, 4, 5, 8}, by decide⟩
  | 9, 8 => ⟨{3, 4, 6, 8}, by decide⟩
  | 10, 0 => ⟨{0, 4, 5, 6}, by decide⟩
  | 10, 1 => ⟨{1, 4, 5, 6}, by decide⟩
  | 10, 2 => ⟨{2, 4, 5, 6}, by decide⟩
  | 10, 3 => ⟨{3, 4, 5, 6}, by decide⟩
  | 10, 4 => ⟨{3, 4, 5, 7}, by decide⟩
  | 10, 5 => ⟨{3, 4, 6, 7}, by decide⟩
  | 10, 6 => ⟨{3, 5, 6, 7}, by decide⟩
  | 10, 7 => ⟨{4, 5, 6, 7}, by decide⟩
  | 10, 8 => ⟨{4, 5, 6, 8}, by decide⟩
  | 11, 0 => ⟨{0, 4, 5, 7}, by decide⟩
  | 11, 1 => ⟨{0, 4, 6, 7}, by decide⟩
  | 11, 2 => ⟨{1, 4, 6, 7}, by decide⟩
  | 11, 3 => ⟨{1, 5, 6, 7}, by decide⟩
  | 11, 4 => ⟨{2, 5, 6, 7}, by decide⟩
  | 11, 5 => ⟨{3, 5, 6, 7}, by decide⟩
  | 11, 6 => ⟨{4, 5, 6, 7}, by decide⟩
  | 11, 7 => ⟨{4, 5, 6, 8}, by decide⟩
  | 11, 8 => ⟨{4, 5, 7, 8}, by decide⟩

def odd_cycle_nine_four_token_fractional_cover_cycle_step (m : Fin 12) (k : ZMod 9) (i : ZMod 9) :
    { s : Finset (ZMod 9) // s.card = 4 } :=
  odd_cycle_nine_four_token_fractional_cover_shift_sub (odd_cycle_nine_four_token_fractional_cover_base_c m ⟨i.val, ZMod.val_lt i⟩) k

theorem odd_cycle_nine_four_token_fractional_cover_cycle_step_valid :
    ∀ (m : Fin 12) (k : ZMod 9) (i : ZMod 9),
      ∃ x ∈ (odd_cycle_nine_four_token_fractional_cover_cycle_step m k i).val,
        (x + 1) ∉ (odd_cycle_nine_four_token_fractional_cover_cycle_step m k i).val ∧
        (odd_cycle_nine_four_token_fractional_cover_cycle_step m k (i + 1)).val =
          insert (x + 1) ((odd_cycle_nine_four_token_fractional_cover_cycle_step m k i).val.erase x) := by
  decide

abbrev OddCycleNineFourTokenFractionalCoverSubtype :=
  { C : Finset { s : Finset (ZMod 9) // s.card = 4 } //
    ∃ c : ZMod 9 → { s : Finset (ZMod 9) // s.card = 4 },
      (∀ i : ZMod 9, ∃ x ∈ (c i).val, (x + 1) ∉ (c i).val ∧ (c (i + 1)).val = insert (x + 1) ((c i).val.erase x)) ∧
      C = Finset.image c Finset.univ }

def odd_cycle_nine_four_token_fractional_cover_cycle_elem (p : Fin 12 × ZMod 9) :
    OddCycleNineFourTokenFractionalCoverSubtype :=
  ⟨Finset.image (odd_cycle_nine_four_token_fractional_cover_cycle_step p.1 p.2) Finset.univ,
   ⟨odd_cycle_nine_four_token_fractional_cover_cycle_step p.1 p.2,
    ⟨odd_cycle_nine_four_token_fractional_cover_cycle_step_valid p.1 p.2, rfl⟩⟩⟩

def odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat : Fin 12 → ℕ
  | 0 => 40
  | 1 => 14
  | 2 => 15
  | 3 => 16
  | 4 => 1
  | 5 => 53
  | 6 => 27
  | 7 => 11
  | 8 => 28
  | 9 => 52
  | 10 => 1
  | 11 => 162

set_option maxRecDepth 100000 in
theorem odd_cycle_nine_four_token_fractional_cover_sum_nat_eq :
    ∀ S : { s : Finset (ZMod 9) // s.card = 4 },
      ∑ p : Fin 12 × ZMod 9,
        (if S ∈ (odd_cycle_nine_four_token_fractional_cover_cycle_elem p).val then
          odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1
        else 0) = 270 := by
  decide +kernel

def odd_cycle_nine_four_token_fractional_cover_weights
    (C : OddCycleNineFourTokenFractionalCoverSubtype) : ℚ :=
  (∑ p : Fin 12 × ZMod 9,
    if odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C then
      (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
    else 0) / 270

/-- The 4-token graph of C_9 admits a uniform fractional winding cycle cover. -/
theorem odd_cycle_nine_four_token_fractional_cover :
    ∃ (weights : { C : Finset { s : Finset (ZMod 9) // s.card = 4 } //
        ∃ c : ZMod 9 → { s : Finset (ZMod 9) // s.card = 4 },
          (∀ i : ZMod 9, ∃ x ∈ (c i).val, (x + 1) ∉ (c i).val ∧ (c (i + 1)).val = insert (x + 1) ((c i).val.erase x)) ∧
          C = Finset.image c Finset.univ } → ℚ),
      (∀ C, 0 ≤ weights C) ∧
      (∀ S : { s : Finset (ZMod 9) // s.card = 4 },
        ∑ C, (if S ∈ C.val then weights C else 0) = 1) := by
  use odd_cycle_nine_four_token_fractional_cover_weights
  constructor
  · intro C
    dsimp [odd_cycle_nine_four_token_fractional_cover_weights]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
    · norm_num
  · intro S
    have h1 : ∀ C : OddCycleNineFourTokenFractionalCoverSubtype,
        (if S ∈ C.val then odd_cycle_nine_four_token_fractional_cover_weights C else 0) =
        (if S ∈ C.val then ∑ p : Fin 12 × ZMod 9,
          if odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C then
            (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
          else 0 else 0) / 270 := by
      intro C
      dsimp [odd_cycle_nine_four_token_fractional_cover_weights]
      split_ifs <;> ring
    simp_rw [h1, ← Finset.sum_div]
    have h2 : ∀ C : OddCycleNineFourTokenFractionalCoverSubtype,
        (if S ∈ C.val then ∑ p : Fin 12 × ZMod 9,
          if odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C then
            (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
          else 0 else 0) =
        ∑ p : Fin 12 × ZMod 9,
          if S ∈ C.val then
            (if odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C then
              (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0 := by
      intro C
      split_ifs with h
      · rfl
      · simp
    simp_rw [h2]
    rw [Finset.sum_comm]
    have h3 : ∀ p : Fin 12 × ZMod 9,
        (∑ C : OddCycleNineFourTokenFractionalCoverSubtype,
          if S ∈ C.val then
            (if odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C then
              (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0) =
        if S ∈ (odd_cycle_nine_four_token_fractional_cover_cycle_elem p).val then
          (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
        else 0 := by
      intro p
      have h4 : ∀ C : OddCycleNineFourTokenFractionalCoverSubtype,
          (if S ∈ C.val then
            (if odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C then
              (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0) =
          if C = odd_cycle_nine_four_token_fractional_cover_cycle_elem p then
            (if S ∈ (odd_cycle_nine_four_token_fractional_cover_cycle_elem p).val then
              (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0 := by
        intro C
        by_cases h : C = odd_cycle_nine_four_token_fractional_cover_cycle_elem p
        · subst h; split_ifs <;> rfl
        · have : ¬(odd_cycle_nine_four_token_fractional_cover_cycle_elem p = C) := fun h' => h h'.symm
          simp [h, this]
      simp_rw [h4, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [h3]
    have h_cast : (∑ p : Fin 12 × ZMod 9,
        if S ∈ (odd_cycle_nine_four_token_fractional_cover_cycle_elem p).val then
          (odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
        else 0) =
        ((∑ p : Fin 12 × ZMod 9,
          if S ∈ (odd_cycle_nine_four_token_fractional_cover_cycle_elem p).val then
            odd_cycle_nine_four_token_fractional_cover_cycle_weight_nat p.1
          else 0 : ℕ) : ℚ) := by
      push_cast; rfl
    rw [h_cast, odd_cycle_nine_four_token_fractional_cover_sum_nat_eq S]
    norm_num
