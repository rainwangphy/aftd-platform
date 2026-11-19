import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTraceable

/-!
# op_1952_isTraceable_of_isHamiltonian

Topic: graphs   Node: 56092f136e1f

Provenance: helper lemma. Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean

Every finite Hamiltonian simple graph on at least two vertices is traceable, since the tail of any Hamiltonian cycle is a Hamiltonian path.
-/

/-- A finite Hamiltonian graph on at least two vertices has a Hamiltonian path. -/
theorem op_1952_isTraceable_of_isHamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hH : G.IsHamiltonian) (hn : 2 ≤ Fintype.card V) :
    G.IsTraceable := by
  obtain ⟨a, p, hp⟩ := hH (by omega)
  exact ⟨p.snd, a, p.tail, hp.isHamiltonian_tail⟩
