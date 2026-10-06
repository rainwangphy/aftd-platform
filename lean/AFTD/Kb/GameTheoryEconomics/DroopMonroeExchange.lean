import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MonroeLoadCompPerm
import AFTD.Kb.GameTheoryEconomics.AssignmentExchange
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore

/-!
# droop_monroe_exchange

Topic: social_choice   Node: 30fe04db1a57

Provenance: helper lemma. step towards droop_monroe_satisfies_droop_pjr_plus (Droop Monroe and Droop-PJR+, Justified Representation: From Hare to Droop, arXiv:2508.00811, Table 1 note a)

Exchange step for Droop assignments: swapping c₀ ∈ W for c ∉ W approved by all of S (no member of S satisfied) gives a Droop-valid assignment scoring at least score(π) + min(|π⁻¹(c₀)|, |S|) - |π⁻¹(c₀) \ S|.
-/

/-- The exchange step for Droop assignments: swapping `c₀ ∈ W` for `c ∉ W` approved by all of `S` (no member of `S` being satisfied by `π`) gives a Droop-valid assignment whose score is at least `score π + min(|π⁻¹(c₀)|, |S|) - |π⁻¹(c₀) \ S|`. -/
theorem droop_monroe_exchange {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m))
    (π : Fin n → Option (Fin m)) (hv : is_droop_valid_assignment k W π) (c₀ c : Fin m)
    (hc₀ : c₀ ∈ W) (hc : c ∉ W) (S : Finset (Fin n)) (hSa : ∀ i ∈ S, c ∈ A i)
    (hun : ∀ i ∈ S, ¬ ∃ d, π i = some d ∧ d ∈ A i) :
    ∃ π', is_droop_valid_assignment k (insert c (W.erase c₀)) π' ∧
      droop_monroe_score A π + min (Finset.univ.filter fun i => π i = some c₀).card S.card ≤
        droop_monroe_score A π' +
          ((Finset.univ.filter fun i => π i = some c₀).filter fun i => i ∉ S).card := by
  obtain ⟨σ, hσ⟩ := assignment_exchange (fun i b => ∃ d, b = some d ∧ d ∈ A i) π (some c₀)
    (some c) S (fun i hi => ⟨c, rfl, hSa i hi⟩) hun
  obtain ⟨hW, hmap, hload, hnone⟩ := hv
  have hπc : ∀ v, π v ≠ some c := fun v h => hc (hmap v c h)
  refine ⟨fun v => if π (σ v) = some c₀ then some c else π (σ v), ⟨?_, ?_, ?_, ?_⟩, hσ⟩
  · have : c ∉ W.erase c₀ := fun h => hc (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem this, Finset.card_erase_of_mem hc₀, hW]
    have : 0 < k := hW ▸ Finset.card_pos.2 ⟨c₀, hc₀⟩
    omega
  · intro v x hx
    simp only at hx
    split_ifs at hx with h
    · cases hx; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, hmap _ _ hx⟩)
      rintro rfl; exact h hx
  · intro d hd
    have key : ∃ e ∈ W, (Finset.univ.filter fun v =>
        (if π (σ v) = some c₀ then some c else π (σ v)) = some d) =
        (Finset.univ.filter fun v => π (σ v) = some e) := by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · refine ⟨c₀, hc₀, Finset.filter_congr fun v _ => ?_⟩
        split_ifs with h
        · simp [h]
        · simp [h, hπc]
      · obtain ⟨hdc, hdW⟩ := Finset.mem_erase.1 hd
        refine ⟨d, hdW, Finset.filter_congr fun v _ => ?_⟩
        split_ifs with h
        · constructor
          · intro h'; cases h'; exact absurd hdW hc
          · intro h'; rw [h] at h'; cases h'; exact absurd rfl hdc
        · rfl
    obtain ⟨e, he, heq⟩ := key
    rw [heq, monroe_load_comp_perm]
    exact hload e he
  · have : (Finset.univ.filter fun v =>
        (if π (σ v) = some c₀ then some c else π (σ v)) = none) =
        (Finset.univ.filter fun v => π (σ v) = none) := by
      refine Finset.filter_congr fun v _ => ?_
      split_ifs with h
      · simp [h]
      · rfl
    rw [this]
    convert (monroe_load_comp_perm π σ none).trans hnone using 2
