import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashOccupiedSlotsCard
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# not_hash_probe_tail_prob_zero_of_lt

Topic: data_structures   Node: b3ed6a15e790

Provenance: original. Related work: refutes `hash_probe_tail_prob_zero_of_lt`

The statement `hash_probe_tail_prob_zero_of_lt` is false: Take n = 1, r = (fun _ => 0 : Fin 1 → ZMod 1), t = 1, k = 2. Hypotheses hold: htn : 1 ≤ 1 and hkt : 1 < 2. But hash_probe_tail_count 1 r 1 2 = 1 (kernel-checked by unfolding the definition), so hash_probe_tail_prob 1 r 1 2 = 1 / 1^2 = 1 ≠ 0. Reason: with t = n the occupied set hash_occupied_slots has cardinality n = |ZMod n|, hence is all of ZMod n, so the condition "p.2 + r j is occupied for all j < k" holds for every pair p whenever k > n; the count is n^(n+1) ≠ 0. The claimed pigeonhole (at most t occupied slots, so fewer than k probes) is only valid when additionally k ≤ n, since the k probe positions p.2 + r 0, …, p.2 + r(k-1) are distinct only if k ≤ n.
-/

theorem not_hash_probe_tail_prob_zero_of_lt : ¬ (∀ (n : ℕ) [NeZero n]
    (r : Fin n → ZMod n) (hr_bij : Function.Bijective r)
    (t k : ℕ) (htn : t ≤ n) (hkt : t < k), hash_probe_tail_prob n r t k = 0) := by
  intro h
  have hbij : Function.Bijective (fun _ : Fin 1 => (0 : ZMod 1)) := by
    constructor
    · intro a b _; exact Subsingleton.elim a b
    · intro b; exact ⟨0, Subsingleton.elim _ b⟩
  have h1 := h 1 (fun _ => 0) hbij 1 2 le_rfl (by norm_num)
  have hc : hash_probe_tail_count 1 (fun _ => 0) 1 2 = 1 := by
    simp only [hash_probe_tail_count]
    have hfilter : (Finset.univ.filter (fun p : (Fin 1 → ZMod 1) × ZMod 1 =>
        ∀ (j : Fin 1), (j:ℕ) < 2 → p.2 + (fun _ => 0) j ∈ hash_occupied_slots 1 (fun _ => 0) (List.ofFn p.1))) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro p _ j _
      have hc' : (hash_occupied_slots 1 (fun _ => 0) (List.ofFn p.1)).card = 1 := by
        rw [hash_occupied_slots_card (n := 1) (r := fun _ => 0) (hr := hbij) (A := List.ofFn p.1) (hA := by simp)]
        simp
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (hash_occupied_slots 1 (fun _ => 0) (List.ofFn p.1)).card)
      rw [show p.2 + (fun _ => (0:ZMod 1)) j = x from Subsingleton.elim _ _]
      exact hx
    rw [hfilter, Finset.card_univ]
    simp
  rw [hash_probe_tail_prob, hc] at h1
  norm_num at h1
