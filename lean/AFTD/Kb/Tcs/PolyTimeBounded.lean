import AFTD.Prelude
import AFTD.Kb.Tcs.TimeBounded

/-!
# PolyTimeBounded

Topic: complexity_basics   Node: 10260c6f5a1f

The class P over alphabet Γ consists of all languages L for which there is a polynomial p : Polynomial ℕ such that L is decidable in time n ↦ p.eval n, i.e. by a Turing machine whose running time on inputs of length n is bounded by p(n).
-/

/-- The complexity class P over the alphabet Γ: languages decidable in polynomial time. -/
def PolyTimeBounded (Γ : Type) (L : Language Γ) : Prop := ∃ p : Polynomial ℕ, TimeBounded Γ (fun n => p.eval n) L
