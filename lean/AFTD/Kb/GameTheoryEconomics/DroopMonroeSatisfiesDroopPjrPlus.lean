import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopMonroeCommittee
import AFTD.Kb.GameTheoryEconomics.IsDroopPjrPlus
import AFTD.Kb.GameTheoryEconomics.DroopMonroeUnsatisfiedGroup

/-!
# droop_monroe_satisfies_droop_pjr_plus

Topic: social_choice   Node: 74137c0da414

Provenance: original. Related work: settles the PJR+ entry for Droop Monroe that Justified Representation: From Hare to Droop, arXiv:2508.00811, Table 1 note a, leaves open (case k + 1 divides n); uses its Lemma 2

If k + 1 divides n, every committee selected by the Droop Monroe rule satisfies Droop-PJR+. This settles the PJR+ entry for Droop Monroe that arXiv:2508.00811 (Table 1, note a) leaves open.
-/

/-- If k + 1 divides n, every committee selected by the Droop Monroe rule satisfies Droop-PJR+. This settles the PJR+ entry for Droop Monroe that arXiv:2508.00811 (Table 1, note a) leaves open. -/
theorem droop_monroe_satisfies_droop_pjr_plus {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ)
    (W : Finset (Fin m)) (hdiv : (k + 1) ∣ n) (hW : is_droop_monroe_committee A k W) :
    is_droop_pjr_plus A k W := by
  obtain ⟨π, hv, hopt⟩ := hW
  intro ℓ hℓ1 _ S hS ⟨c, hcW, hcS⟩
  by_contra hlt
  push Not at hlt
  set q := n / (k + 1) with hq
  have hn : n = (k + 1) * q := (Nat.mul_div_cancel' hdiv).symm
  have hceil : (n + k) / (k + 1) = q := by
    rw [hn, add_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos k),
      Nat.div_eq_of_lt (Nat.lt_succ_self k), zero_add]
  set WS := W.filter fun c => ∃ i ∈ S, c ∈ A i with hWS
  set Sat := S.filter fun i => ∃ d, π i = some d ∧ d ∈ A i with hSat
  set S' := S.filter fun i => ¬ ∃ d, π i = some d ∧ d ∈ A i with hS'
  -- satisfied members of `S` sit in the at most `ℓ - 1` seats of `WS`, `q` voters each
  have hSat_le : Sat.card ≤ q * (WS.image some).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := π)
    · intro i hi
      obtain ⟨hiS, d, hd, hdA⟩ := Finset.mem_filter.1 hi
      rw [hd]
      exact Finset.mem_image_of_mem _
        (Finset.mem_filter.2 ⟨hv.2.1 i d hd, i, hiS, hdA⟩)
    · intro b hb
      obtain ⟨d, hdWS, rfl⟩ := Finset.mem_image.1 hb
      have hdW : d ∈ W := (Finset.mem_filter.1 hdWS).1
      calc (Sat.filter fun i => π i = some d).card
          ≤ (Finset.univ.filter fun i => π i = some d).card :=
            Finset.card_le_card fun i hi => by simp [(Finset.mem_filter.1 hi).2]
        _ ≤ q := hceil ▸ (hv.2.2.1 d hdW).2
  have himg : (WS.image some).card ≤ ℓ - 1 := (Finset.card_image_le).trans (by omega)
  have hsplit : Sat.card + S'.card = S.card := Finset.card_filter_add_card_filter_not _
  have hbig : ℓ * q < S.card := by
    have : (k + 1) * (ℓ * q) < (k + 1) * S.card := by
      calc (k + 1) * (ℓ * q) = ℓ * n := by rw [hn]; ring
        _ < _ := hS
    exact Nat.lt_of_mul_lt_mul_left this
  have hSat' : Sat.card ≤ q * (ℓ - 1) := hSat_le.trans (Nat.mul_le_mul_left _ himg)
  have hS'big : q < S'.card := by
    have : q * (ℓ - 1) + q = ℓ * q := by
      rw [mul_comm ℓ q]; cases ℓ with
      | zero => omega
      | succ l => simp [Nat.mul_succ]
    omega
  exact droop_monroe_unsatisfied_group A k W π hdiv hv hopt S' hS'big
    (fun i hi => (Finset.mem_filter.1 hi).2) c hcW
    (fun i hi => hcS i (Finset.mem_filter.1 hi).1)
