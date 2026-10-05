import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTGate

/-!
# clifford_t_gate_matrix

Topic: quantum   Node: 938baf61de31

The matrix of a Clifford+T gate in the computational basis indexed by bit strings x : Fin N -> Bool: H on qubit i has entry (-1)^{x_i y_i}/sqrt 2 when x and y agree off i and 0 otherwise; S and T are diagonal with phase i, resp. e^{i pi/4}, when qubit i is 1; CNOT(c, t) is the permutation matrix of y -> y with bit t flipped by bit c.
-/

/-- The matrix of a Clifford+T gate in the computational basis Fin N -> Bool. -/
noncomputable def clifford_t_gate_matrix {N : ℕ} : CliffordTGate N → Matrix (Fin N → Bool) (Fin N → Bool) ℂ := fun
  | .h i => fun x y =>
      if ∀ j, j ≠ i → x j = y j then (if x i && y i then -1 else 1) / (Real.sqrt 2 : ℂ) else 0
  | .s i => Matrix.diagonal fun x => if x i then Complex.I else 1
  | .cnot c t _ => fun x y => if x = Function.update y t (xor (y t) (y c)) then 1 else 0
  | .t i => Matrix.diagonal fun x =>
      if x i then Complex.exp (Real.pi / 4 * Complex.I) else 1
