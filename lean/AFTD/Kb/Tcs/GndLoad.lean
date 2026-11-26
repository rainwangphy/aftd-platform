import AFTD.Prelude

/-!
# gnd_load

Topic: online_algorithms   Node: 1c286f1807f6

Provenance: formalization of a published result. Source: arXiv:2611.30912 Section 1.1

Given a type E with decidable equality, an implicit natural number N, a reply function reply : Fin N → Finset E, and a weight function w : Fin N → E → ℝ, gnd_load reply w defines the function from E to ℝ mapping each e : E to the sum over all i : Fin N of (if e ∈ reply i then w i e else 0).
-/

/-- Total load on each resource induced by a sequence of replies and request weights. -/
noncomputable def gnd_load {E : Type*} [DecidableEq E] {N : ℕ} (reply : Fin N → Finset E) (w : Fin N → E → ℝ) : E → ℝ := fun e => ∑ i : Fin N, if e ∈ reply i then w i e else 0
