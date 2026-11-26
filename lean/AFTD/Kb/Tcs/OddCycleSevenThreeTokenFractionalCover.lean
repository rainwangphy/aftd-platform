import AFTD.Prelude
import AFTD.Kb.Tcs.C

/-!
# odd_cycle_seven_three_token_fractional_cover

Topic: graphs   Node: a2a09b29de57

Provenance: original. Related work: arXiv:2611.22830

There exists a function assigning a nonnegative rational weight to each vertex set C of a directed 7-cycle in the 3-token graph of Z/7Z (where an arc replaces some x in S with x+1 when x+1 is unoccupied) such that every 3-subset S of Z/7Z has sum of weights of cycles containing S equal to 1.
-/

open Finset

lemma odd_cycle_seven_three_token_fractional_cover_shift_set_card (s : Finset (ZMod 7)) (k : ZMod 7) (h : s.card = 3) :
    (s.image (· + k)).card = 3 := by
  rw [card_image_of_injective s (fun a b hab => add_right_cancel hab), h]

def odd_cycle_seven_three_token_fractional_cover_shift_sub (s : { s : Finset (ZMod 7) // s.card = 3 }) (k : ZMod 7) :
    { s : Finset (ZMod 7) // s.card = 3 } :=
  ⟨s.val.image (· + k), odd_cycle_seven_three_token_fractional_cover_shift_set_card s.val k s.property⟩

def odd_cycle_seven_three_token_fractional_cover_base_c : Fin 3 → Fin 7 → { s : Finset (ZMod 7) // s.card = 3 }
  | 0, 0 => ⟨{0, 2, 4}, by decide⟩
  | 0, 1 => ⟨{0, 2, 5}, by decide⟩
  | 0, 2 => ⟨{1, 2, 5}, by decide⟩
  | 0, 3 => ⟨{1, 3, 5}, by decide⟩
  | 0, 4 => ⟨{1, 3, 6}, by decide⟩
  | 0, 5 => ⟨{2, 3, 6}, by decide⟩
  | 0, 6 => ⟨{2, 4, 6}, by decide⟩
  | 1, 0 => ⟨{3, 4, 5}, by decide⟩
  | 1, 1 => ⟨{3, 4, 6}, by decide⟩
  | 1, 2 => ⟨{0, 3, 4}, by decide⟩
  | 1, 3 => ⟨{0, 3, 5}, by decide⟩
  | 1, 4 => ⟨{1, 3, 5}, by decide⟩
  | 1, 5 => ⟨{1, 4, 5}, by decide⟩
  | 1, 6 => ⟨{2, 4, 5}, by decide⟩
  | 2, 0 => ⟨{0, 1, 2}, by decide⟩
  | 2, 1 => ⟨{0, 1, 3}, by decide⟩
  | 2, 2 => ⟨{0, 2, 3}, by decide⟩
  | 2, 3 => ⟨{1, 2, 3}, by decide⟩
  | 2, 4 => ⟨{1, 2, 4}, by decide⟩
  | 2, 5 => ⟨{1, 2, 5}, by decide⟩
  | 2, 6 => ⟨{1, 2, 6}, by decide⟩

def odd_cycle_seven_three_token_fractional_cover_cycle_step (m : Fin 3) (k : ZMod 7) (i : ZMod 7) :
    { s : Finset (ZMod 7) // s.card = 3 } :=
  odd_cycle_seven_three_token_fractional_cover_shift_sub
    (odd_cycle_seven_three_token_fractional_cover_base_c m ⟨i.val, ZMod.val_lt i⟩) k

lemma odd_cycle_seven_three_token_fractional_cover_cycle_step_valid :
    ∀ (m : Fin 3) (k : ZMod 7) (i : ZMod 7),
      ∃ x ∈ (odd_cycle_seven_three_token_fractional_cover_cycle_step m k i).val,
        (x + 1) ∉ (odd_cycle_seven_three_token_fractional_cover_cycle_step m k i).val ∧
        (odd_cycle_seven_three_token_fractional_cover_cycle_step m k (i + 1)).val =
          insert (x + 1) ((odd_cycle_seven_three_token_fractional_cover_cycle_step m k i).val.erase x) := by
  decide

abbrev OddCycleSevenThreeTokenFractionalCoverSubtype :=
  { C : Finset { s : Finset (ZMod 7) // s.card = 3 } //
    ∃ c : ZMod 7 → { s : Finset (ZMod 7) // s.card = 3 },
      (∀ i : ZMod 7, ∃ x ∈ (c i).val, (x + 1) ∉ (c i).val ∧ (c (i + 1)).val = insert (x + 1) ((c i).val.erase x)) ∧
      C = Finset.image c Finset.univ }

def odd_cycle_seven_three_token_fractional_cover_cycle_elem (p : Fin 3 × ZMod 7) :
    OddCycleSevenThreeTokenFractionalCoverSubtype :=
  ⟨Finset.image (odd_cycle_seven_three_token_fractional_cover_cycle_step p.1 p.2) Finset.univ,
   ⟨odd_cycle_seven_three_token_fractional_cover_cycle_step p.1 p.2,
    ⟨odd_cycle_seven_three_token_fractional_cover_cycle_step_valid p.1 p.2, rfl⟩⟩⟩

def odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat : Fin 3 → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 3

lemma odd_cycle_seven_three_token_fractional_cover_sum_nat_eq_seven :
    ∀ S : { s : Finset (ZMod 7) // s.card = 3 },
      ∑ p : Fin 3 × ZMod 7,
        (if S ∈ (odd_cycle_seven_three_token_fractional_cover_cycle_elem p).val then
          odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1
        else 0) = 7 := by
  decide

def odd_cycle_seven_three_token_fractional_cover_weights
    (C : OddCycleSevenThreeTokenFractionalCoverSubtype) : ℚ :=
  (∑ p : Fin 3 × ZMod 7,
    if odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C then
      (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
    else 0) / 7

/-- The 3-token graph of C_7 admits a uniform fractional winding cycle cover. -/
theorem odd_cycle_seven_three_token_fractional_cover :
    ∃ (weights : { C : Finset { s : Finset (ZMod 7) // s.card = 3 } //
        ∃ c : ZMod 7 → { s : Finset (ZMod 7) // s.card = 3 },
          (∀ i : ZMod 7, ∃ x ∈ (c i).val, (x + 1) ∉ (c i).val ∧ (c (i + 1)).val = insert (x + 1) ((c i).val.erase x)) ∧
          C = Finset.image c Finset.univ } → ℚ),
      (∀ C, 0 ≤ weights C) ∧
      (∀ S : { s : Finset (ZMod 7) // s.card = 3 },
        ∑ C, (if S ∈ C.val then weights C else 0) = 1) := by
  use odd_cycle_seven_three_token_fractional_cover_weights
  constructor
  · intro C
    dsimp [odd_cycle_seven_three_token_fractional_cover_weights]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
    · norm_num
  · intro S
    have h1 : ∀ C : OddCycleSevenThreeTokenFractionalCoverSubtype,
        (if S ∈ C.val then odd_cycle_seven_three_token_fractional_cover_weights C else 0) =
        (if S ∈ C.val then ∑ p : Fin 3 × ZMod 7,
          if odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C then
            (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
          else 0 else 0) / 7 := by
      intro C
      dsimp [odd_cycle_seven_three_token_fractional_cover_weights]
      split_ifs <;> ring
    simp_rw [h1, ← Finset.sum_div]
    have h2 : ∀ C : OddCycleSevenThreeTokenFractionalCoverSubtype,
        (if S ∈ C.val then ∑ p : Fin 3 × ZMod 7,
          if odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C then
            (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
          else 0 else 0) =
        ∑ p : Fin 3 × ZMod 7,
          if S ∈ C.val then
            (if odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C then
              (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0 := by
      intro C
      split_ifs with h
      · rfl
      · simp
    simp_rw [h2]
    rw [Finset.sum_comm]
    have h3 : ∀ p : Fin 3 × ZMod 7,
        (∑ C : OddCycleSevenThreeTokenFractionalCoverSubtype,
          if S ∈ C.val then
            (if odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C then
              (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0) =
        if S ∈ (odd_cycle_seven_three_token_fractional_cover_cycle_elem p).val then
          (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
        else 0 := by
      intro p
      have h4 : ∀ C : OddCycleSevenThreeTokenFractionalCoverSubtype,
          (if S ∈ C.val then
            (if odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C then
              (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0) =
          if C = odd_cycle_seven_three_token_fractional_cover_cycle_elem p then
            (if S ∈ (odd_cycle_seven_three_token_fractional_cover_cycle_elem p).val then
              (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
            else 0)
          else 0 := by
        intro C
        by_cases h : C = odd_cycle_seven_three_token_fractional_cover_cycle_elem p
        · subst h; split_ifs <;> rfl
        · have : ¬(odd_cycle_seven_three_token_fractional_cover_cycle_elem p = C) := fun h' => h h'.symm
          simp [h, this]
      simp_rw [h4, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [h3]
    have h_cast : (∑ p : Fin 3 × ZMod 7,
        if S ∈ (odd_cycle_seven_three_token_fractional_cover_cycle_elem p).val then
          (odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1 : ℚ)
        else 0) =
        ((∑ p : Fin 3 × ZMod 7,
          if S ∈ (odd_cycle_seven_three_token_fractional_cover_cycle_elem p).val then
            odd_cycle_seven_three_token_fractional_cover_cycle_weight_nat p.1
          else 0 : ℕ) : ℚ) := by
      push_cast; rfl
    rw [h_cast, odd_cycle_seven_three_token_fractional_cover_sum_nat_eq_seven S]
    norm_num
