import AFTD.Prelude

/-!
# biased_bit_critical_cost

Topic: information   Node: 8ba3f90a0021

Provenance: formalization of a published result. Source: arXiv:2611.16066 Thm 5.4

For a bias parameter p : ℝ, biased_bit_critical_cost p is defined as the real infimum (sInf) of the set of values (l : ℝ) + a * (2 * a ^ l - 1) / (1 - a) for l : ℕ, where a = (1 - p) / p.
-/

/-- Critical cost c_crit(p) for additive integer masks against a biased bit with parameter p. -/
noncomputable def biased_bit_critical_cost (p : ℝ) : ℝ := let a := (1 - p) / p
  sInf (Set.range fun (l : ℕ) => (l : ℝ) + a * (2 * a ^ l - 1) / (1 - a))
