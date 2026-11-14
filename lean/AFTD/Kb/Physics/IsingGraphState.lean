import AFTD.Prelude
import AFTD.Kb.Tcs.Hn

/-!
# ising_graph_state

Topic: quantum_mechanics   Node: d34f1f8a2fbe

Provenance: formalization of a published result. Source: OP-1695; arXiv:2610.27080

For a graph G on n vertices with edge angles θ, the Ising graph state psi_G is exp(-i sum_{uv in E} θ_uv Z_u Z_v) |+⟩^{⊗ n}, with amplitude on computational basis bitstring x given by (1 / sqrt(2^n)) exp(-i sum_{uv in E} θ_uv (-1)^{x_u + x_v}).
-/

open scoped Classical in
/-- The Ising graph quantum state exp(-i ∑ θ_uv Z_u Z_v) |+⟩^{⊗ n}. -/
noncomputable def ising_graph_state (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (θ : Sym2 (Fin n) → ℝ) : Hn n := EuclideanSpace.equiv (Fin n → Fin 2) ℂ |>.symm (fun x =>
    (1 / Real.sqrt (2 ^ n : ℝ) : ℂ) *
    Complex.exp (- Complex.I * ∑ e ∈ G.edgeFinset,
      ((θ e : ℂ) * Sym2.lift ⟨fun u v => if x u = x v then (1 : ℂ) else (-1 : ℂ),
                             fun u v => by simp [eq_comm]⟩ e)))
