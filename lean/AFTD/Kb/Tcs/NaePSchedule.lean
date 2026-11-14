import AFTD.Prelude

/-!
# nae_p_schedule

Topic: quantum   Node: b55040056688

Provenance: formalization of a published result. Source: arXiv:1211.0721, Section 3.3, Lemmas 1–3: abstract reachability encoding of their p-computation rules

The least inductive relation on triples (d, θ, q), where d is a natural number and θ and q are real numbers, contains (0, π, 1) and is closed under: composition (d, θ, q) ↦ (d+1, arccos(1−(4/9)(1−cos θ)²), 2q); amplification (d, θ, q) ↦ (d, arccos(cos(cθ)), cq) for any positive natural number c, coerced to a real number; and relaxation (d, θ, q) ↦ (d, θ′, q) for any real θ′ with 0 ≤ θ′ ≤ θ. Here q is explicitly a real-valued scheduled query budget, not a lower bound on arbitrary quantum circuits.
-/

inductive nae_p_schedule : ℕ → ℝ → ℝ → Prop
  | initial : nae_p_schedule 0 Real.pi 1
  | compose {d : ℕ} {θ q : ℝ} : nae_p_schedule d θ q →
      nae_p_schedule (d + 1)
        (Real.arccos (1 - (4 / 9 : ℝ) * (1 - Real.cos θ) ^ 2)) (2 * q)
  | amplify {d : ℕ} {θ q : ℝ} (c : ℕ) : 0 < c → nae_p_schedule d θ q →
      nae_p_schedule d (Real.arccos (Real.cos ((c : ℝ) * θ))) ((c : ℝ) * q)
  | relax {d : ℕ} {θ q θ' : ℝ} : 0 ≤ θ' → θ' ≤ θ → nae_p_schedule d θ q →
      nae_p_schedule d θ' q
