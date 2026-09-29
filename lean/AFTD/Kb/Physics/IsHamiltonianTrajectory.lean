import AFTD.Prelude

/-!
# IsHamiltonianTrajectory

Topic: classical_mechanics   Node: 5efb13cc9a53

A path γ : ℝ → E × E is a Hamiltonian trajectory for the Hamiltonian H : E × E → ℝ if for all times t, the time derivative of the position component equals the momentum gradient of H at γ(t) and the time derivative of the momentum component equals the negative position gradient of H at γ(t).
-/

/-- A trajectory in phase space satisfies Hamilton's canonical equations of motion with Hamiltonian H. -/
def IsHamiltonianTrajectory {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E × E → ℝ) (γ : ℝ → E × E) : Prop :=
  ∀ t : ℝ,
    deriv (fun s => (γ s).1) t = gradient (𝕜 := ℝ) (F := E) (fun p => H ((γ t).1, p)) (γ t).2 ∧
    deriv (fun s => (γ s).2) t = - gradient (𝕜 := ℝ) (F := E) (fun q => H (q, (γ t).2)) (γ t).1
