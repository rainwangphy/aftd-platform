import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.LinearProbeOffset

/-!
# linear_probing_displacements

Topic: online_algorithms   Node: 3b97d3a3912e

Provenance: formalization of a published result. Source: scout/2610-31363-a-sharp-analysis-of-fixed-offset-hash-tables.md

Given a table size n and a sequence of n home slots h in Fin n -> ZMod n, linear_probing_displacements n h i is the number of occupied slots inspected by insertion i before finding an empty slot under linear probing.
-/

/-- Vector of displacements (number of occupied slots inspected before the first empty slot) for each sequential insertion in an n-slot circular hash table under linear probing. -/
def linear_probing_displacements (n : ℕ) [NeZero n] (h : Fin n → ZMod n) : Fin n → ℕ :=
  fun i =>
    let T := hash_occupied_slots n (linear_probe_offset n) ((List.ofFn h).take i.val)
    let candidates := Finset.univ.filter (fun j : Fin n => h i + (j : ZMod n) ∉ T)
    if hc : candidates.Nonempty then (candidates.min' hc).val else 0
