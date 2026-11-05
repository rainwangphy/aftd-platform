import AFTD.Prelude
import AFTD.Kb.Tcs.OMSRArrival

/-!
# probeValue

Topic: online_algorithms   Node: 68509e1295e2

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:415

Given arrival arr with success probabilities arr.prob, resource weights w, continuation value function V on subsets of resources, and available resources S, probeValue recursively computes the expected reward of probing sequence L: on empty sequence it yields V S; on probing i :: L, with probability arr.prob i it matches i yielding reward w i + V (S.erase i), and with probability 1 - arr.prob i it continues to probe sequence L.
-/

/-- Expected reward from probing a list of resources sequentially for an arrival. -/
def probeValue {n : ℕ} (arr : OMSRArrival n) (w : Fin n → ℝ) (V : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    List (Fin n) → ℝ
  | [] => V S
  | i :: L => arr.prob i * (w i + V (S.erase i)) + (1 - arr.prob i) * probeValue arr w V S L
