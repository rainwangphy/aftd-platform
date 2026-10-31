import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.PauliLabel
import AFTD.Kb.Tcs.ApplyCliffordGate

/-!
# apply_clifford_circuit

Topic: quantum   Node: bab31798ef5c

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:453

The symplectic action of a Clifford circuit circ : List (CliffordGate k) on a PauliLabel k, obtained by folding apply_clifford_gate across circ from left to right.
-/

/-- Action of a Clifford circuit on a Pauli label. -/
def apply_clifford_circuit {k : ℕ} (circ : List (CliffordGate k)) (p : PauliLabel k) : PauliLabel k := circ.foldl (fun acc g => apply_clifford_gate g acc) p
