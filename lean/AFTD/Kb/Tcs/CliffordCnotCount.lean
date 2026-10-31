import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordGate

/-!
# clifford_cnot_count

Topic: quantum   Node: d3c73ca53768

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1658

The CNOT count of a k-qubit Clifford circuit, defined as the number of cnot gates in the list circ : List (CliffordGate k).
-/

/-- The CNOT count of a k-qubit Clifford circuit. -/
def clifford_cnot_count {k : ℕ} (circ : List (CliffordGate k)) : ℕ := (circ.filter fun g => match g with | .cnot _ _ _ => true | _ => false).length
