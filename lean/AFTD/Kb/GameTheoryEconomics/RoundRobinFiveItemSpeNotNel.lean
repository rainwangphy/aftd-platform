import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickGameIsSpe
import AFTD.Kb.GameTheoryEconomics.PickGameRootAllocation
import AFTD.Kb.GameTheoryEconomics.IsNelPd
import AFTD.Kb.GameTheoryEconomics.PickGameMovePayoff
import AFTD.Kb.GameTheoryEconomics.PickGameMoveZero

/-!
# round_robin_five_item_spe_not_nel

Topic: fair_division   Node: a3ec82ae79ed

Provenance: helper lemma. The round-robin interpretation of OP-1323, arXiv:2611.09685 Section 7; finite search experiment 20540.

For two agents with identical item values 16, 8, 4, 2 and 1 and the round-robin order 0,1,0,1,0, there is a subgame-perfect continuation profile whose first agent receives items 0,2,4 and whose allocation fails NEL under pairwise dominance.
-/

open Finset

def round_robin_five_item_u_nat : Fin 5 → ℕ := ![16, 8, 4, 2, 1]

def round_robin_five_item_count_true (b : Fin 5 → Bool) : Nat :=
  ((List.finRange 5).filter b).length

def round_robin_five_item_min_true (b : Fin 5 → Bool) : Option (Fin 5) :=
  ((List.finRange 5).filter b).head?

def round_robin_five_item_s_picker (step : Nat) : Fin 2 :=
  if step = 0 then 0
  else if step = 1 then 1
  else if step = 2 then 0
  else if step = 3 then 1
  else 0

def round_robin_five_item_b_erase (b : Fin 5 → Bool) (x : Fin 5) : Fin 5 → Bool :=
  fun y => if y = x then false else b y

def round_robin_five_item_g_fuel : Nat → (Fin 5 → Bool) → (Fin 5 → Bool)
| 0, _ => fun _ => false
| fuel + 1, b =>
  match round_robin_five_item_min_true b with
  | none => fun _ => false
  | some m =>
    let b' := round_robin_five_item_b_erase b m
    let rest := round_robin_five_item_g_fuel fuel b'
    let step := 5 - round_robin_five_item_count_true b
    if round_robin_five_item_s_picker step = 0 then
      fun x => if x = m then true else rest x
    else
      rest

def round_robin_five_item_g_alloc (b : Fin 5 → Bool) : Fin 5 → Bool :=
  round_robin_five_item_g_fuel 5 b

def round_robin_five_item_G_finset (R : Finset (Fin 5)) : Finset (Fin 5) :=
  Finset.filter (fun x => round_robin_five_item_g_alloc (fun y => decide (y ∈ R)) x) Finset.univ

def round_robin_five_item_F_alloc (h : List (Fin 5)) : Finset (Fin 5) :=
  round_robin_five_item_G_finset (Finset.univ \ h.toFinset)

def round_robin_five_item_move_zero_finset (R : Finset (Fin 5)) (x : Fin 5) : Finset (Fin 5) :=
  if ([0, 1, 0, 1, 0] : List (Fin 2)).getD (5 - R.card) 0 = 0 then
    insert x (round_robin_five_item_G_finset (R.erase x))
  else
    round_robin_five_item_G_finset (R.erase x)

def round_robin_five_item_payoff_nat (R : Finset (Fin 5)) (x : Fin 5) : ℕ :=
  let p := ([0, 1, 0, 1, 0] : List (Fin 2)).getD (5 - R.card) 0
  let A := round_robin_five_item_move_zero_finset R x
  ∑ z ∈ (if p = 0 then A else R \ A), round_robin_five_item_u_nat z

theorem round_robin_five_item_spe_for_all_R : ∀ R : Finset (Fin 5),
    round_robin_five_item_G_finset R ⊆ R ∧
    if R.Nonempty then
      ∃ x ∈ R, round_robin_five_item_G_finset R = round_robin_five_item_move_zero_finset R x ∧
        ∀ y ∈ R, round_robin_five_item_payoff_nat R y ≤ round_robin_five_item_payoff_nat R x
    else
      round_robin_five_item_G_finset R = ∅ := by
  decide

lemma round_robin_five_item_h_len_eq {h : List (Fin 5)} (hnodup : h.Nodup) :
    h.length = 5 - (Finset.univ \ h.toFinset : Finset (Fin 5)).card := by
  have h1 : (Finset.univ \ h.toFinset : Finset (Fin 5)).card = 5 - h.toFinset.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have h2 : h.toFinset.card = h.length := List.toFinset_card_of_nodup hnodup
  have h3 : h.length ≤ 5 := by
    rw [← h2]
    exact Finset.card_le_univ h.toFinset
  omega

lemma round_robin_five_item_rem_erase_eq {h : List (Fin 5)} {x : Fin 5}
    (_hx : x ∈ Finset.univ \ h.toFinset) :
    Finset.univ \ (h ++ [x]).toFinset = (Finset.univ \ h.toFinset).erase x := by
  ext y
  simp

lemma round_robin_five_item_move_zero_eq {h : List (Fin 5)} (hnodup : h.Nodup) {x : Fin 5}
    (hx : x ∈ Finset.univ \ h.toFinset) :
    pick_game_move_zero [0, 1, 0, 1, 0] round_robin_five_item_F_alloc h x =
    round_robin_five_item_move_zero_finset (Finset.univ \ h.toFinset) x := by
  dsimp [pick_game_move_zero, round_robin_five_item_move_zero_finset, round_robin_five_item_F_alloc]
  rw [round_robin_five_item_h_len_eq hnodup, round_robin_five_item_rem_erase_eq hx]

lemma round_robin_five_item_u_val_eq (x : Fin 5) :
    (![16, 8, 4, 2, 1] : Fin 5 → ℝ) x = (round_robin_five_item_u_nat x : ℝ) := by
  fin_cases x <;> simp [round_robin_five_item_u_nat]

lemma round_robin_five_item_payoff_eq {h : List (Fin 5)} (hnodup : h.Nodup) {x : Fin 5}
    (hx : x ∈ Finset.univ \ h.toFinset) :
    pick_game_move_payoff (fun _ => (![16, 8, 4, 2, 1] : Fin 5 → ℝ))
      [0, 1, 0, 1, 0] round_robin_five_item_F_alloc h x =
    (round_robin_five_item_payoff_nat (Finset.univ \ h.toFinset) x : ℝ) := by
  dsimp [pick_game_move_payoff, round_robin_five_item_payoff_nat]
  rw [round_robin_five_item_h_len_eq hnodup, round_robin_five_item_move_zero_eq hnodup hx]
  push_cast
  exact Finset.sum_congr rfl (fun z _ => round_robin_five_item_u_val_eq z)

lemma round_robin_five_item_is_spe :
    pick_game_is_spe (fun _ => (![16, 8, 4, 2, 1] : Fin 5 → ℝ))
      [0, 1, 0, 1, 0] round_robin_five_item_F_alloc := by
  constructor
  · rfl
  · intro h hnodup
    let R := Finset.univ \ h.toFinset
    have hR := round_robin_five_item_spe_for_all_R R
    obtain ⟨hsub, hif⟩ := hR
    refine ⟨hsub, ?_⟩
    by_cases hne : R.Nonempty
    · rw [if_pos hne] at hif ⊢
      obtain ⟨x, hx, heq, hopt⟩ := hif
      refine ⟨x, hx, ?_, ?_⟩
      · change round_robin_five_item_G_finset R = _
        rw [heq, ← round_robin_five_item_move_zero_eq hnodup hx]
      · intro y hy
        rw [round_robin_five_item_payoff_eq hnodup hy, round_robin_five_item_payoff_eq hnodup hx]
        exact Nat.cast_le.mpr (hopt y hy)
    · rw [if_neg hne] at hif ⊢
      exact hif

lemma round_robin_five_item_hFroot :
    round_robin_five_item_F_alloc [] = {0, 2, 4} := by
  decide

lemma round_robin_five_item_not_nel :
    ¬ is_nel_pd (fun (_ : Fin 2) (x y : Fin 5) => (![16, 8, 4, 2, 1] : Fin 5 → ℝ) x ≤ (![16, 8, 4, 2, 1] : Fin 5 → ℝ) y)
      (pick_game_root_allocation round_robin_five_item_F_alloc) := by
  intro h
  have hA0 : pick_game_root_allocation round_robin_five_item_F_alloc 0 = {0, 2, 4} := by
    simp [pick_game_root_allocation, round_robin_five_item_hFroot]
  have hA1 : pick_game_root_allocation round_robin_five_item_F_alloc 1 = {1, 3} := by
    simp [pick_game_root_allocation, round_robin_five_item_hFroot]
    ext x; fin_cases x <;> decide
  have hlt : (pick_game_root_allocation round_robin_five_item_F_alloc 1).card <
      (pick_game_root_allocation round_robin_five_item_F_alloc 0).card := by
    rw [hA0, hA1]; decide
  have hy : (4 : Fin 5) ∈ pick_game_root_allocation round_robin_five_item_F_alloc 0 := by
    rw [hA0]; simp
  obtain ⟨f, hfA, -, hpref⟩ := h 1 0 hlt 4 hy
  have h0 : (0 : Fin 5) ∈ (pick_game_root_allocation round_robin_five_item_F_alloc 0).erase 4 := by
    rw [hA0]; simp
  have hf0 : f 0 ∈ pick_game_root_allocation round_robin_five_item_F_alloc 1 := hfA 0 h0
  rw [hA1] at hf0
  have hpref0 := hpref 0 h0
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf0
  rcases hf0 with hf0 | hf0
  · rw [hf0] at hpref0
    have : (![16, 8, 4, 2, 1] : Fin 5 → ℝ) 0 = 16 := by rfl
    have : (![16, 8, 4, 2, 1] : Fin 5 → ℝ) 1 = 8 := by rfl
    linarith
  · rw [hf0] at hpref0
    have : (![16, 8, 4, 2, 1] : Fin 5 → ℝ) 0 = 16 := by rfl
    have : (![16, 8, 4, 2, 1] : Fin 5 → ℝ) 3 = 2 := by rfl
    linarith

theorem round_robin_five_item_spe_not_nel :
  ∃ F : List (Fin 5) → Finset (Fin 5),
    pick_game_is_spe (fun _ => (![16, 8, 4, 2, 1] : Fin 5 → ℝ)) [0, 1, 0, 1, 0] F ∧
    F [] = {0, 2, 4} ∧
    ¬ is_nel_pd (fun (_ : Fin 2) (x y : Fin 5) => (![16, 8, 4, 2, 1] : Fin 5 → ℝ) x ≤ (![16, 8, 4, 2, 1] : Fin 5 → ℝ) y) (pick_game_root_allocation F) := ⟨round_robin_five_item_F_alloc, round_robin_five_item_is_spe, round_robin_five_item_hFroot, round_robin_five_item_not_nel⟩
