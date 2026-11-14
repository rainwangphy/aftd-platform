import AFTD.Prelude

/-!
# subsample_prob

Topic: online_algorithms   Node: 12eb8a15b8a1

Provenance: formalization of a published result. Source: arXiv:2611.15711, Section 2.1

The probability of obtaining subset s of Fin n under independent subsampling where each of the n items is included independently with probability r.
-/

open Finset in
/-- Probability of retaining a given subset under independent rate-r subsampling. -/
def subsample_prob (n : ℕ) (r : ℝ) (s : Finset (Fin n)) : ℝ := r ^ s.card * (1 - r) ^ (n - s.card)
