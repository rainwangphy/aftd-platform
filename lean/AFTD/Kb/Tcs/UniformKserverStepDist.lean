import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverServes

/-!
# uniform_kserver_step_dist

Topic: online_algorithms   Node: fb307b57e40c

Provenance: formalization of a published result. Source: arXiv:2610.37192 Section 3.2

For a natural number k, a family of spaces M indexed by Fin k with decidable equality, a request r, a normalized finitely supported configuration distribution μ : (∀ i, M i) →₀ ℝ, and a current configuration x, uniform_kserver_step_dist k r μ x is the finitely supported transition distribution of type (∀ i, M i) →₀ ℝ: if x serves r it returns Finsupp.single x 1; otherwise it returns the sum over all i : Fin k of Finsupp.single (Function.update x i (r i)) (1 / (2 * k)), plus (1 / 2 : ℝ) • μ.
-/

/-- Step transition distribution of the randomized online algorithm. -/
noncomputable def uniform_kserver_step_dist (k : ℕ) {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (r : ∀ i, M i) (μ : (∀ i, M i) →₀ ℝ) (x : ∀ i, M i) : (∀ i, M i) →₀ ℝ := by
  classical
  exact if uniform_kserver_serves x r then
    Finsupp.single x 1
  else
    (∑ i : Fin k, Finsupp.single (Function.update x i (r i)) (1 / (2 * (k : ℝ)))) +
      (1 / 2 : ℝ) • μ
