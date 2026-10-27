import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionCharacteristic

/-!
# redistribution_characteristic_entire

Topic: mechanism_design   Node: 9f8d3a03302b

Provenance: helper lemma. Routine finite-characteristic-function helper for IN-251, arXiv:2610.10995 Lemma4.3 Steps1/2 and equation12. These statements do not assert the half-plane boundary integral inequality or the main harmonic error bound. No research advance.

The empirical characteristic function is entire for every finite real report profile.
-/

open Finset MeasureTheory

theorem redistribution_characteristic_entire {n : ℕ} (θ : Fin n → ℝ) :
    AnalyticOnNhd ℂ (redistribution_characteristic θ) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  unfold redistribution_characteristic
  fun_prop
