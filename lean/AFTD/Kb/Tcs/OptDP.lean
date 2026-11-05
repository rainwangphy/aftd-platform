import AFTD.Prelude
import AFTD.Kb.Tcs.OMSRArrival
import AFTD.Kb.Tcs.OfflineArrival

/-!
# optDP

Topic: online_algorithms   Node: 24e2977c77f2

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:420

For resource weights w : Fin n → ℝ, fuel : ℕ, available resources S : Finset (Fin n), and arrival states arrs : Fin m → OfflineArrival n, optDP is the dynamic programming value function: 0 when fuel is 0, and otherwise the maximum of 0 and the supremum over valid probes of arrival t and available resource i of p * (w i + optDP w fuel (S.erase i) arrs_succ) + (1 - p) * optDP w fuel S arrs_fail.
-/

/-- Dynamic programming value of the adaptive offline benchmark. -/
noncomputable def optDP {n m : ℕ} (w : Fin n → ℝ) :
    ℕ → Finset (Fin n) → (Fin m → OfflineArrival n) → ℝ
  | 0, _, _ => 0
  | fuel + 1, S, arrs =>
    let continue_val := ⨆ (t : Fin m) (i : Fin n)
      (_ : i ∈ S ∧ ¬ (arrs t).matched ∧ i ∉ (arrs t).probed ∧ (arrs t).probed.card < (arrs t).arrival.patience),
      let p := (arrs t).arrival.prob i
      let arrs_succ : Fin m → OfflineArrival n :=
        fun j => if j = t then { (arrs t) with matched := true } else arrs j
      let arrs_fail : Fin m → OfflineArrival n :=
        fun j => if j = t then { (arrs t) with probed := insert i (arrs t).probed } else arrs j
      p * (w i + optDP w fuel (S.erase i) arrs_succ) + (1 - p) * optDP w fuel S arrs_fail
    max 0 continue_val
