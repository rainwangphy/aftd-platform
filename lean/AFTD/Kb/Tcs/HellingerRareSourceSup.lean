import AFTD.Prelude
import AFTD.Kb.Tcs.HellingerRareSourceRatio

/-!
# hellinger_rare_source_sup

Topic: information   Node: 97762767672d

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the Subadditivity of Mutual f-Information)

For a natural number k : ℕ, hellinger_rare_source_sup k is the supremum of the rare-source Hellinger ratio function hellinger_rare_source_ratio k u over all u in the half-open interval Set.Ico 0 1.
-/

/-- Supremum of the rare-source Hellinger ratio F_k(u) over u in [0, 1) -/
noncomputable def hellinger_rare_source_sup (k : ℕ) : ℝ := sSup (hellinger_rare_source_ratio k '' Set.Ico 0 1)
