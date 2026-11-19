import AFTD.Prelude

/-!
# sampfordWeight

Topic: social_choice   Node: 66a6bdb89f27

Provenance: helper lemma. step towards sampford_consecutive_house_coupling_loss_delta_four

The Sampford (unnormalized) weight of a set S of parties for a residue vector r, matching Eq. (2) of Correa et al. (arXiv:2405.03687): (sum over i in S of (1 - r_i)) times the product of r_i over S times the product of (1 - r_i) over the complement of S.
-/

open Classical in
/-- Sampford's unnormalized set weight for a residue vector. -/
noncomputable def sampfordWeight {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, (1 - r i)) * (∏ i ∈ S, r i) * (∏ i ∈ (Finset.univ \ S), (1 - r i))
