import AFTD.Prelude
import AFTD.Kb.Tcs.PhiMorphism

/-!
# phi_iter

Topic: combinatorics   Node: 326188305cf1

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 1

For a positive integer k with proof hk : 0 < k, the n-th iterate phi_iter k hk n of phi_morphism k starting from [0] is defined recursively by phi_iter k hk 0 = [0] and phi_iter k hk (n + 1) = (phi_iter k hk n).flatMap (phi_morphism k).
-/

/-- The finite prefix sequence obtained by iterating phi_k starting from [0]. -/
def phi_iter (k : ℕ) (hk : 0 < k) : ℕ → List (Fin k)
| 0 => [⟨0, hk⟩]
| n + 1 => (phi_iter k hk n).flatMap (phi_morphism k)
