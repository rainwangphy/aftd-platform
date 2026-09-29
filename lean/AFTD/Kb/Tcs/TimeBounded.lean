import AFTD.Prelude

/-!
# TimeBounded

Topic: complexity_basics   Node: 0da68775a133

A language L over an alphabet Γ is decidable in time T (T : ℕ → ℕ) if there is a total decider f : List Γ → Bool together with a Turing machine M computing f, such that M runs for at most T n steps on every input of length n, and f agrees with the characteristic function of L: for every word w, w ∈ L iff f w = true.
-/

/-- A language is decidable in time T if some Turing machine decider runs within T n steps on inputs of length n and decides it. -/
def TimeBounded (Γ : Type) (T : ℕ → ℕ) (L : Language Γ) : Prop := ∃ (f : List Γ → Bool),
    (∃ M : Turing.TM2ComputableInTime (id : List Γ → List Γ) Computability.encodeBool f,
      ∀ n, M.time n ≤ T n) ∧
    ∀ w, w ∈ L ↔ f w = true
