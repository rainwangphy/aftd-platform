import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTCircuitMatrix
import AFTD.Kb.Tcs.CliffordTGate

/-!
# implements_ccz_layer

Topic: quantum   Node: 52c7cb9c439c

Provenance: formalization of a published result. Source: Exact T-counts of Toffoli Layers from an Isotropy Bound, arXiv:2610.01024, abstract and Sec. 1 (implementing the parallel CCZ layer with clean ancillas, the setting of its open problem on circuits with Hadamards)

A Clifford+T circuit on 3m + a qubits implements the layer U_m of m disjoint CCZ gates with a clean ancillas if, for some global phase e^{i theta} and every input x of 3m bits, it maps |x, 0^a> to e^{i theta} (-1)^{#{j : x_{3j} = x_{3j+1} = x_{3j+2} = 1}} |x, 0^a> (all other output amplitudes zero), so the ancillas return to |0>.
-/

/-- A circuit on 3m + a qubits implements the layer of m disjoint CCZ gates with a clean ancillas: up to a global phase it maps |x, 0> to (-1)^{sum_j x_{3j} x_{3j+1} x_{3j+2}} |x, 0> for every input x. -/
def implements_ccz_layer (m a : ℕ) (gs : List (CliffordTGate (3 * m + a))) : Prop :=
  ∃ θ : ℝ, ∀ (x : Fin (3 * m) → Bool) (z : Fin (3 * m + a) → Bool),
    clifford_t_circuit_matrix gs z (fun i => if h : i.val < 3 * m then x ⟨i.val, h⟩ else false) =
      if z = (fun i => if h : i.val < 3 * m then x ⟨i.val, h⟩ else false) then
        Complex.exp (θ * Complex.I) *
          (-1) ^ ((Finset.univ.filter fun j : Fin m =>
            x ⟨3 * j.val, by omega⟩ && x ⟨3 * j.val + 1, by omega⟩ &&
              x ⟨3 * j.val + 2, by omega⟩).card)
      else 0
