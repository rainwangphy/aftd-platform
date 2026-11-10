import AFTD.Prelude
import AFTD.Kb.Tcs.IsTspTour
import AFTD.Kb.Tcs.TspTourLength

/-!
# tsp_opt

Topic: approximation   Node: 058f7bdddee8

Provenance: formalization of a published result. Source: arXiv:2611.09421 Section 1

OPT is the infimum length of a tour on V under edge weights ℓ.
-/

/-- OPT is the infimum length of a tour on V under edge weights ℓ. -/
noncomputable def tsp_opt {V : Type*} [Fintype V] [DecidableEq V] (ℓ : V → V → ℝ) : ℝ := sInf {tsp_tour_length ℓ σ | (σ : Equiv.Perm V) (_ : is_tsp_tour σ)}
