import AFTD.Prelude
import AFTD.Kb.Tcs.CommutingQuantumMessageSector

/-!
# commuting_quantum_message_sector_span

Topic: communication   Node: 9cdc85ba56c2

Provenance: helper lemma. step towards commuting_quantum_efficiency_one_bit

For Alice's one-bit effects $A^0, A^1$, the message-$m$ sector space $H_m$ is the closed span of all message-$m$ sectors $V_{m,t}$, $t \in [N]$; it is a closed subspace of the shared Hilbert space.
-/

def commuting_quantum_message_sector_span
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (A : Fin N → Fin 2 → E →L[ℝ] E) (m : Fin 2) : ClosedSubmodule ℝ E :=
  ⟨(⨆ t : Fin N, commuting_quantum_message_sector A m t).topologicalClosure,
    Submodule.isClosed_topologicalClosure _⟩
