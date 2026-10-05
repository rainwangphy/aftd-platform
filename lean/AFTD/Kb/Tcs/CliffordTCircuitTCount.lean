import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTGate

/-!
# clifford_t_circuit_t_count

Topic: quantum   Node: bc8b89a82e72

The T-count of a Clifford+T circuit: the number of T gates in its gate list.
-/

/-- The number of T gates of a circuit. -/
def clifford_t_circuit_t_count {N : ℕ} (gs : List (CliffordTGate N)) : ℕ :=
  gs.countP fun g => match g with
    | .t _ => true
    | _ => false
