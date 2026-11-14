import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonAttackingQueens
import AFTD.Kb.Tcs.ModularQueensAttack

/-!
# op_1592_zmod2_queens_card_le_one

Topic: combinatorics   Node: 444da548fb7f

Provenance: formalization of a published result. Source: arXiv:2611.14754 Sec. 1

On any d-dimensional modular board (Z/2Z)^d, any set of mutually non-attacking queens has cardinality at most 1.
-/

def op_1592_zmod2_queens_card_le_one_to_sign (a : ZMod 2) : SignType :=
  if a = 0 then SignType.zero else SignType.pos

lemma op_1592_zmod2_queens_card_le_one_to_sign_cast (a : ZMod 2) :
    (SignType.cast (op_1592_zmod2_queens_card_le_one_to_sign a) : ZMod 2) = a := by
  revert a; decide

lemma op_1592_zmod2_queens_card_le_one_to_sign_eq_zero_iff (a : ZMod 2) :
    op_1592_zmod2_queens_card_le_one_to_sign a = 0 ↔ a = 0 := by
  revert a; decide

lemma op_1592_zmod2_queens_card_le_one_attack_of_ne {d : ℕ} (x y : Fin d → ZMod 2) (h : x ≠ y) :
    modular_queens_attack x y := by
  unfold modular_queens_attack
  use 1
  use fun i => op_1592_zmod2_queens_card_le_one_to_sign (x i - y i)
  refine ⟨by decide, ?_, ?_⟩
  · intro hv
    apply h
    ext i
    have hi : op_1592_zmod2_queens_card_le_one_to_sign (x i - y i) = 0 := congr_fun hv i
    rw [op_1592_zmod2_queens_card_le_one_to_sign_eq_zero_iff, sub_eq_zero] at hi
    exact hi
  · intro i
    rw [op_1592_zmod2_queens_card_le_one_to_sign_cast, one_mul]

/-- On (Z/2Z)^d, every mutually non-attacking queens configuration has size at most 1. -/
theorem op_1592_zmod2_queens_card_le_one {d : ℕ} (s : Finset (Fin d → ZMod 2))
    (hs : is_non_attacking_queens s) : s.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  by_contra h
  have hatt := op_1592_zmod2_queens_card_le_one_attack_of_ne a b h
  exact hs ha hb h hatt
