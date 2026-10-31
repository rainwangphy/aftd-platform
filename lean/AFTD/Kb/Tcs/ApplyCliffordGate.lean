import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.PauliLabel

/-!
# apply_clifford_gate

Topic: quantum   Node: 5c2fa3a555fc

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:453

The symplectic action of a Clifford gate g : CliffordGate k on a PauliLabel k: h i swaps the x and z components at qubit i; s i updates the z component at qubit i by adding the x component; and cnot c t _ adds the x component at control c to target t, and adds the z component at target t to control c.
-/

/-- Symplectic action of a Clifford gate on a binary Pauli label. -/
def apply_clifford_gate {k : ℕ} (g : CliffordGate k) (p : PauliLabel k) : PauliLabel k := match g with
  | .h i => (Function.update p.1 i (p.2 i), Function.update p.2 i (p.1 i))
  | .s i => (p.1, Function.update p.2 i (p.2 i + p.1 i))
  | .cnot c t _ => (Function.update p.1 t (p.1 t + p.1 c), Function.update p.2 c (p.2 c + p.2 t))
