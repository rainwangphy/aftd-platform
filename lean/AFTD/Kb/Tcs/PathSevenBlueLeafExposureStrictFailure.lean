import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort
import AFTD.Kb.Tcs.PathSevenBlueLeafExposureNotUlc

/-!
# path_seven_blue_leaf_exposure_strict_failure

Topic: graphs   Node: 6b3df763398f

Provenance: helper lemma.

On a seven-vertex path with an endpoint fixed blue, the root-exposure mixture at weight three quarters violates the binomial-normalized log-concavity inequality.
-/

theorem path_seven_blue_leaf_exposure_strict_failure : (let T := SimpleGraph.pathGraph 7; let p : Fin 7 := 1; let b : Fin 7 := 0; let a := fun k : ℕ => {S : Finset (Fin 7) | b ∉ S ∧ S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧ ¬ zero_forcing_root_exposed_fort T p S}.ncard; let c := fun k : ℕ => {S : Finset (Fin 7) | b ∉ S ∧ S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧ zero_forcing_root_exposed_fort T p S}.ncard; (4 * a 5 + 3 * c 5) ^ 2 * Nat.choose 6 4 * Nat.choose 6 6 < (4 * a 4 + 3 * c 4) * (4 * a 6 + 3 * c 6) * Nat.choose 6 5 ^ 2) := by
  have h := path_seven_blue_leaf_exposure_not_ulc
  dsimp only at h ⊢
  rcases h with ⟨h4, h5, h6⟩
  rw [h4, h5, h6]
  norm_num [Nat.choose]
