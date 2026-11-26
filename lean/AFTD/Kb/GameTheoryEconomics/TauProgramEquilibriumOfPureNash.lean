import AFTD.Prelude

/-!
# tau_program_equilibrium_of_pure_nash

Topic: equilibria   Node: c6ca25508011

Provenance: formalization of a published result. Source: arXiv:2611.33193 Theorem 2.9

Let A, Prog, and Signal be types, run : Prog → Signal → A an execution function, τ₁, τ₂ : Prog → Signal transparency maps, u₁, u₂ : A → A → ℝ payoff functions, and const_prog : A → Prog a constant program map satisfying run (const_prog a) μ = a for all a : A and μ : Signal. If (a₁, a₂) is a pure Nash equilibrium of the base game (∀ x, u₁ x a₂ ≤ u₁ a₁ a₂ and ∀ y, u₂ a₁ y ≤ u₂ a₁ a₂), then the profile of constant programs (const_prog a₁, const_prog a₂) is a pure τ-program equilibrium of the meta-game: for every deviation π₁' : Prog by player 1, u₁ (run π₁' (τ₁ (const_prog a₂))) (run (const_prog a₂) (τ₂ π₁')) ≤ u₁ (run (const_prog a₁) (τ₁ (const_prog a₂))) (run (const_prog a₂) (τ₂ (const_prog a₁))), and for every deviation π₂' : Prog by player 2, u₂ (run (const_prog a₁) (τ₁ π₂')) (run π₂' (τ₂ (const_prog a₁))) ≤ u₂ (run (const_prog a₁) (τ₁ (const_prog a₂))) (run (const_prog a₂) (τ₂ (const_prog a₁))).
-/

/-- Pure Nash equilibria induce pure tau-program equilibria via constant programs. -/
theorem tau_program_equilibrium_of_pure_nash
    {A Prog Signal : Type*}
    (run : Prog → Signal → A) (τ₁ τ₂ : Prog → Signal)
    (u₁ u₂ : A → A → ℝ)
    (const_prog : A → Prog)
    (h_const : ∀ (a : A) (μ : Signal), run (const_prog a) μ = a)
    (a₁ a₂ : A)
    (h_nash₁ : ∀ x : A, u₁ x a₂ ≤ u₁ a₁ a₂)
    (h_nash₂ : ∀ y : A, u₂ a₁ y ≤ u₂ a₁ a₂) :
    (∀ π₁' : Prog, u₁ (run π₁' (τ₁ (const_prog a₂))) (run (const_prog a₂) (τ₂ π₁')) ≤
      u₁ (run (const_prog a₁) (τ₁ (const_prog a₂))) (run (const_prog a₂) (τ₂ (const_prog a₁)))) ∧
    (∀ π₂' : Prog, u₂ (run (const_prog a₁) (τ₁ π₂')) (run π₂' (τ₂ (const_prog a₁))) ≤
      u₂ (run (const_prog a₁) (τ₁ (const_prog a₂))) (run (const_prog a₂) (τ₂ (const_prog a₁)))) := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
