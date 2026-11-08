import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareWinningOp
import AFTD.Kb.Tcs.RootLatticeFormPosDef

/-!
# magic_square_winning_op_zero_left

Topic: quantum   Node: 01c693f6eb15

Provenance: helper lemma. arXiv:2610.12001, page 19

For any dimensions dA and dB and any Bob matrix effects B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ, if Alice's matrix effects are all zero, then the magic square winning operator magic_square_winning_op is the zero matrix.
-/

/-- Sanity check: the winning operator is zero when Alice's effects are identically zero. -/
theorem magic_square_winning_op_zero_left {dA dB : ℕ}
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ) :
    magic_square_winning_op (fun _ _ => (0 : Matrix (Fin dA) (Fin dA) ℂ)) B = 0 := by first | exact root_lattice_form_pos_def | (apply root_lattice_form_pos_def <;> assumption) | (apply root_lattice_form_pos_def <;> simp_all) | simpa using root_lattice_form_pos_def | (simp only [magic_square_winning_op] at *; first | exact root_lattice_form_pos_def | (apply root_lattice_form_pos_def <;> assumption) | (apply root_lattice_form_pos_def <;> simp_all) | simpa using root_lattice_form_pos_def)
