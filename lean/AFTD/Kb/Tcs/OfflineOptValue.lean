import AFTD.Prelude
import AFTD.Kb.Tcs.OptDP
import AFTD.Kb.Tcs.OfflineArrival
import AFTD.Kb.Tcs.OMSRArrival

/-!
# offlineOptValue

Topic: online_algorithms   Node: f939eb549086

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:420

The expected reward of the adaptive offline benchmark OPT on a list of arrivals arrs with resource weights w, defined by running optDP with fuel equal to arrs.length * n starting from the full resource set univ and initial unprobed, unmatched arrival states.
-/

/-- Expected reward of the adaptive offline benchmark OPT. -/
noncomputable def offlineOptValue {n : ℕ} (w : Fin n → ℝ) (arrs : List (OMSRArrival n)) : ℝ :=
  let m := arrs.length
  let init_arrs : Fin m → OfflineArrival n :=
    fun idx => { arrival := arrs.get idx, probed := ∅, matched := false }
  optDP w (m * n) Finset.univ init_arrs
