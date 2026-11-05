import AFTD.Prelude
import AFTD.Kb.Tcs.ProbeValue
import AFTD.Kb.Tcs.OMSRArrival

/-!
# onlinePolicyValue

Topic: online_algorithms   Node: 16438f73cd48

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:416

The expected total reward of a deterministic online policy π on an arrival list arrs starting from available resources S with resource weights w, defined by folding probeValue along arrs.
-/

/-- Expected reward of a deterministic online policy on a list of arrivals. -/
def onlinePolicyValue {n : ℕ} (w : Fin n → ℝ)
    (π : OMSRArrival n → Finset (Fin n) → List (Fin n)) :
    List (OMSRArrival n) → Finset (Fin n) → ℝ
  | [], _ => 0
  | arr :: rest, S =>
    probeValue arr w (fun S' => onlinePolicyValue w π rest S') S (π arr S)
