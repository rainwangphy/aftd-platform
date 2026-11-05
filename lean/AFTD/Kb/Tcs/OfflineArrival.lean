import AFTD.Prelude
import AFTD.Kb.Tcs.OMSRArrival

/-!
# OfflineArrival

Topic: online_algorithms   Node: 91c78bcbf88a

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:417

The state of an arrival in the offline benchmark, tracking its arrival data, the set of resources already probed for it, and whether it has been matched.
-/

/-- Arrival state in the adaptive offline benchmark. -/
structure OfflineArrival (n : ℕ) where
  arrival : OMSRArrival n
  probed : Finset (Fin n)
  matched : Bool
