import AFTD.Prelude
import AFTD.Kb.Tcs.OMSRArrival

/-!
# IsValidProbeSeq

Topic: online_algorithms   Node: c8e7a46df5b6

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:1173

A list of offline resources is a valid probe sequence for an arrival from available resources if it has no duplicates, all its resources are currently available, and its length does not exceed the arrival's patience budget.
-/

/-- Validity of a probe sequence from available resources within patience budget. -/
def IsValidProbeSeq {n : ℕ} (arr : OMSRArrival n) (S : Finset (Fin n)) (L : List (Fin n)) : Prop :=
  L.Nodup ∧ (∀ i ∈ L, i ∈ S) ∧ L.length ≤ arr.patience
