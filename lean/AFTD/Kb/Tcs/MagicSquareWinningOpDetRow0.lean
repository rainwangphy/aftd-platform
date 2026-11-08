import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareWinningOp

/-!
# magic_square_winning_op_det_row0

Topic: quantum   Node: 6c3117d820d2

Provenance: formalization of a published result. Source: arXiv:2610.12001, page 19, line 1029

Given dimensions dA and dB, Alice's matrix effects A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ, Bob's matrix effects B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ, and an answer string k : Fin 3 → Bool, the deterministic row-0 winning operator is the winning operator magic_square_winning_op where Alice's row-0 measurement is replaced by the deterministic output k: that is, Alice's effects on row 0 are the identity matrix if s = k and 0 otherwise, while for rows x ≠ 0 they remain A x s.
-/

/-- The winning operator for the magic square game where Alice's row 0 measurement is replaced by the deterministic output k. -/
noncomputable def magic_square_winning_op_det_row0 {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ := magic_square_winning_op (fun x s => if x = 0 then (if s = k then 1 else 0) else A x s) B
