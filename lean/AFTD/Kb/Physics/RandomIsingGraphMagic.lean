import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLiouvilleMomentTwo
import AFTD.Kb.Physics.IsingGraphState

/-!
# random_ising_graph_magic

Topic: quantum_mechanics   Node: a3952f32c4c4

Provenance: formalization of a published result. Source: arXiv:2610.27080, Rényi multi-entropy of graph states and the n -> 1 limit

For a natural number n and a simple graph G on Fin n, random_ising_graph_magic n G is defined as 2^n times the second Pauli-Liouville moment of the Ising graph state on G with uniform edge angles Real.pi / 8.
-/

open scoped Classical in
/-- The normalized stabilizer Pauli fourth moment X_n(G) = 2^n Q(G) for the Ising graph state at edge angle pi/8. -/
noncomputable def random_ising_graph_magic (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ := 2 ^ n * pauliLiouvilleMomentTwo n (ising_graph_state n G (fun _ => Real.pi / 8))
