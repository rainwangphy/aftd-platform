import AFTD.Prelude

/-!
# efx_scaled_perturbation

Topic: fair_division   Node: 28eb3846bdeb

Provenance: helper lemma. Nondegenerate strengthening of the OP-7 no-self three-split obstruction, experiments 11492–11494; related perturbation argument arXiv:2002.05119 Lemma 1.

Scale the original natural valuations by K and add a nonnegative natural perturbation.
-/

def efx_scaled_perturbation {n m : ℕ} (K : ℕ) (v d : Fin n → Fin m → ℕ) : Fin n → Fin m → ℕ := fun i g => K * v i g + d i g
