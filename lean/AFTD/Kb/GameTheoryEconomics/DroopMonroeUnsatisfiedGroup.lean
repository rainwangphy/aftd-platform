import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopValidAssignment
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore
import AFTD.Kb.GameTheoryEconomics.DroopMonroeExchange

/-!
# droop_monroe_unsatisfied_group

Topic: social_choice   Node: e4dec9eeef49

Lemma 2 of Casey–Elkind: if (k+1) divides n and π is an optimal Droop-valid assignment for W, no group of more than n/(k+1) voters, all unsatisfied by π, jointly approves a candidate outside W.
-/

/-- Casey–Elkind's Lemma 2 for the Droop Monroe rule, in the form used here: if `(k+1) ∣ n` and `π` is an optimal Droop-valid assignment for `W`, no group of more than `n/(k+1)` voters, none of them satisfied by `π`, jointly approves a candidate outside `W`. -/
theorem droop_monroe_unsatisfied_group {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ)
    (W : Finset (Fin m)) (π : Fin n → Option (Fin m)) (hdiv : (k + 1) ∣ n)
    (hv : is_droop_valid_assignment k W π)
    (hopt : ∀ W' π', is_droop_valid_assignment k W' π' →
      droop_monroe_score A π' ≤ droop_monroe_score A π)
    (S : Finset (Fin n)) (hS : n / (k + 1) < S.card)
    (hun : ∀ i ∈ S, ¬ ∃ d, π i = some d ∧ d ∈ A i) (c : Fin m) (hc : c ∉ W)
    (hSa : ∀ i ∈ S, c ∈ A i) : False := by
  set q := n / (k + 1) with hq
  have hn : n = (k + 1) * q := (Nat.mul_div_cancel' hdiv).symm
  have hceil : (n + k) / (k + 1) = q := by
    rw [hn, add_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos k),
      Nat.div_eq_of_lt (Nat.lt_succ_self k), zero_add]
  -- some member of `S` is assigned to a real candidate
  obtain ⟨i₀, hi₀S, hi₀⟩ : ∃ i ∈ S, π i ≠ none := by
    by_contra hall
    push Not at hall
    have : S ⊆ Finset.univ.filter fun i => π i = none := fun i hi => by simp [hall i hi]
    have := Finset.card_le_card this
    rw [hv.2.2.2] at this
    omega
  obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.1 hi₀
  have hc₀W : c₀ ∈ W := hv.2.1 i₀ c₀ hc₀
  obtain ⟨π', hv', hsc⟩ := droop_monroe_exchange A k W π hv c₀ c hc₀W hc S hSa hun
  have hle := hopt _ π' hv'
  set R := Finset.univ.filter fun i => π i = some c₀ with hR
  have hRc : R.card = q := le_antisymm (hceil ▸ (hv.2.2.1 c₀ hc₀W).2) (hv.2.2.1 c₀ hc₀W).1
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (p := fun i => i ∈ S)
  have hin : 0 < (R.filter fun i => i ∈ S).card :=
    Finset.card_pos.2 ⟨i₀, by simp [hR, hc₀, hi₀S]⟩
  have hmin : min R.card S.card = q := by rw [hRc]; omega
  rw [hmin] at hsc
  omega
