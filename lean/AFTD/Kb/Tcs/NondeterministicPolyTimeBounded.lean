import AFTD.Prelude
import AFTD.Kb.Tcs.TimeBounded
import AFTD.Kb.Tcs.PairEncode

/-!
# NondeterministicPolyTimeBounded

Topic: complexity_basics   Node: ab44855bd66d

A language L over Γ is in NP in verifier form if there are a polynomial p and a language V of words over Γ ⊕ Unit such that V is decidable in time n ↦ p.eval n and, for every word w, w ∈ L holds if and only if there exists a certificate word c over Γ with c.length ≤ p (w.length) and pairEncode w c ∈ V.
-/

/-- The class NP in verifier form: membership is witnessed by a polynomially bounded certificate checked in polynomial time. -/
def NondeterministicPolyTimeBounded (Γ : Type) (L : Language Γ) : Prop := ∃ (p : Polynomial ℕ) (V : Language (Γ ⊕ Unit)),
    TimeBounded (Γ ⊕ Unit) (fun n => p.eval n) V ∧
      ∀ w : List Γ, w ∈ L ↔ ∃ c : List Γ, c.length ≤ p.eval w.length ∧ pairEncode w c ∈ V
