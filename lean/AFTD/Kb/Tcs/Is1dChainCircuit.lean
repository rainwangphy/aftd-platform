import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordGate

/-!
# is_1d_chain_circuit

Topic: quantum   Node: f200c56ee642

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1668

A Clifford circuit circ : List (CliffordGate k) satisfies the 1D nearest-neighbor chain connectivity condition if every cnot gate with control c and target t satisfies c.val + 1 = t.val or t.val + 1 = c.val.
-/

/-- Predicate that a Clifford circuit on k qubits has 1D nearest-neighbor chain connectivity. -/
def is_1d_chain_circuit {k : ℕ} (circ : List (CliffordGate k)) : Prop := circ.all (fun g => match g with | .cnot c t _ => decide (c.val + 1 = t.val ∨ t.val + 1 = c.val) | _ => true) = true
