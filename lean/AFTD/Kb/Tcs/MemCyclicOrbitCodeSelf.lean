import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicOrbitCode

/-!
# mem_cyclic_orbit_code_self

Topic: information   Node: 1f9ca0f87292

Provenance: helper lemma. folklore

Every F-subspace U of L belongs to its own cyclic orbit code $\mathcal{C}_L(U)$.
-/

/-- A subspace U belongs to its own cyclic orbit code. -/
theorem mem_cyclic_orbit_code_self (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L]
    (U : Submodule F L) :
    U ∈ cyclic_orbit_code F U := ⟨1, one_ne_zero, by ext; simp⟩
