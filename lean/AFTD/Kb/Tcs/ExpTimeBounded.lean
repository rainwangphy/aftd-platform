import AFTD.Prelude
import AFTD.Kb.Tcs.TimeBounded

/-!
# ExpTimeBounded

Topic: complexity_basics   Node: d5400c251050

The class EXP over alphabet Γ consists of all languages L for which there is a polynomial p such that L is decidable in time n ↦ 2 ^ (p.eval n), i.e. by a Turing machine whose running time on inputs of length n is bounded by 2^(p(n)).
-/

/-- The complexity class EXP over the alphabet Γ: languages decidable in exponential time. -/
def ExpTimeBounded (Γ : Type) (L : Language Γ) : Prop := ∃ p : Polynomial ℕ, TimeBounded Γ (fun n => 2 ^ p.eval n) L
