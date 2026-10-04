import AFTD.Prelude

/-!
# is_prop1_fair

Topic: fair_division   Node: ca944fc54865

An allocation is PROP1-fair to an agent with valuation v and entitlement w if her bundle A has v(A) >= w v(M), or v(A + g) > w v(M) for some item g outside A, or v(A - c) > w v(M) for some item c in A.
-/

/-- PROP1 (arXiv:2502.02815, Def. 5, strict form): the agent's bundle reaches the proportional share `w · v([m])`, or beats it after taking one more item, or after giving one away. -/
def is_prop1_fair {m : ℕ} (v : Finset (Fin m) → ℝ) (w : ℝ) (A : Finset (Fin m)) : Prop :=
  w * v Finset.univ ≤ v A ∨ (∃ g, g ∉ A ∧ w * v Finset.univ < v (insert g A)) ∨
    ∃ c ∈ A, w * v Finset.univ < v (A.erase c)
