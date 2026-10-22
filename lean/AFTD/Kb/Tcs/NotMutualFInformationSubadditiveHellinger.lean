import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformationSubadditive
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.MutualHellingerInformationNotSubadditive
import AFTD.Kb.Tcs.PowerDivergenceGenerator

/-!
# not_mutual_f_information_subadditive_hellinger

Topic: information   Node: 85dc326dc767

Provenance: helper lemma. arXiv:2610.21231, Section II

The mutual f-information is not subadditive for the Hellinger generator (power divergence with parameter 1/2).
-/

/-- The Hellinger generator (power divergence with parameter 1/2) is not subadditive for mutual f-information. -/
theorem not_mutual_f_information_subadditive_hellinger :
    ¬ mutual_f_information_subadditive (power_divergence_generator (1 / 2)) := by
  intro h
  obtain ⟨pX, PY, PZ, hX0, hX1, hY0, hY1, hZ0, hZ1, hlt⟩ := mutual_hellinger_information_not_subadditive
  have hle := h (Fin 2) (Fin 2) (Fin 2) pX PY PZ hX0 hX1 hY0 hY1 hZ0 hZ1
  linarith
