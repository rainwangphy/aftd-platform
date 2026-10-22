import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFKs

/-!
# subadditive_ks_identity

Topic: information   Node: 68caf2913d8f

Provenance: helper lemma. arXiv:2610.21231, Appendix C

For real numbers α and x and functions s, g : ℝ → ℝ, if g x = α * x + s x, deriv g x - α = deriv s x, and deriv (deriv g) x = deriv (deriv s) x, then g x + 2 * (deriv g x - α)^2 / (- deriv (deriv g) x) = α * x + subadditive_f_ks s x.
-/

/-- Pointwise algebraic identity connecting g and K_s: g(x) + 2(g'(x) - α)^2 / (-g''(x)) = α x + K_s(x). -/
theorem subadditive_ks_identity (α x : ℝ) (s g : ℝ → ℝ)
    (hg : g x = α * x + s x)
    (hg' : deriv g x - α = deriv s x)
    (hg'' : deriv (deriv g) x = deriv (deriv s) x) :
    g x + 2 * (deriv g x - α) ^ 2 / (- deriv (deriv g) x) =
      α * x + subadditive_f_ks s x := by
  unfold subadditive_f_ks
  rw [hg, hg', hg'']
  ring
