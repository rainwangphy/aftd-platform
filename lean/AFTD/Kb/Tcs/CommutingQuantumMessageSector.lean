import AFTD.Prelude

/-!
# commuting_quantum_message_sector

Topic: communication   Node: e9072cf5edff

Provenance: helper lemma. step towards commuting_quantum_efficiency_one_bit

For Alice's one-bit effects $A^0, A^1$ and a message $m \in \{0,1\}$, the message-$m$ sector of label $t$ is the subspace of vectors annihilated by every Alice effect $A^m_s$ with $s \ne t$: $V_{m,t} = \{v : \forall s \ne t,\ A^m_s v = 0\}$.
-/

/-- Message-m sector of label t: the vectors killed by every Alice effect for the other labels. -/
def commuting_quantum_message_sector
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (A : Fin N → Fin 2 → E →L[ℝ] E) (m : Fin 2) (t : Fin N) : Submodule ℝ E where
  carrier := {v | ∀ s : Fin N, s ≠ t → A s m v = 0}
  add_mem' := by
    intro x y hx hy s hs
    simp [map_add, hx s hs, hy s hs]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx s hs
    simp [map_smul, hx s hs]
