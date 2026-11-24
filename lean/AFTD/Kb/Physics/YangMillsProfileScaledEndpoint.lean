import AFTD.Prelude

/-!
# yang_mills_profile_scaled_endpoint

Topic: classical_fields   Node: e422f74bc95a

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:152

For a natural number dimension d : ℕ and a real endpoint value c : ℝ, the scaled endpoint quantity is yang_mills_profile_scaled_endpoint d c = ((d : ℝ) - 5) * (1 - c^2) / 2.
-/

/-- The scaled endpoint quantity F(d, c) = (d - 5)(1 - c^2)/2 associated with endpoint value c = u(1). -/
noncomputable def yang_mills_profile_scaled_endpoint (d : ℕ) (c : ℝ) : ℝ := (d - 5 : ℝ) * (1 - c^2) / 2
