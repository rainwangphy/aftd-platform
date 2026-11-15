import AFTD.Prelude
import AFTD.Kb.Tcs.PhiIter

/-!
# u_word

Topic: combinatorics   Node: ec83bd605be8

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 1

For a positive integer k with proof hk : 0 < k, the infinite word u_word k hk : ℕ → Fin k is the fixed point of phi_morphism k, where the m-th letter is the m-th element of phi_iter k hk (m + 1).
-/

/-- The infinite fixed point u_k of the morphism phi_k. -/
def u_word (k : ℕ) (hk : 0 < k) (m : ℕ) : Fin k := (phi_iter k hk (m + 1)).getD m ⟨0, hk⟩
