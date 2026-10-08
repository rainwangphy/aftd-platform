import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsDroopMonroeCommittee
import AFTD.Kb.GameTheoryEconomics.IsDroopJr
import AFTD.Kb.GameTheoryEconomics.DroopMonroeScore
import AFTD.Kb.GameTheoryEconomics.DroopMonroeExchange

/-!
# droop_monroe_satisfies_droop_jr

Topic: social_choice   Node: b80458c627bc

Provenance: original. Related work: arXiv:2508.00811, Table 1

Every committee W of size k selected by the Droop Monroe rule satisfies Droop-JR: every voter group S of size strictly greater than n/(k+1) that jointly approves some candidate contains a voter who approves at least one candidate in W.
-/

/-- Every winning committee under the Droop Monroe rule satisfies Droop-JR for all n and k. -/
theorem droop_monroe_satisfies_droop_jr (n m : ℕ) (A : Fin n → Finset (Fin m)) (k : ℕ)
    (W : Finset (Fin m)) (hW : is_droop_monroe_committee A k W) :
    is_droop_jr A k W := by
  intro S hS ⟨c, hc⟩
  by_contra hno
  push Not at hno
  obtain ⟨π, hv, hopt⟩ := hW
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos S.card with h | h
    · rw [h] at hS; simp at hS
    · exact h
  have hcW : c ∉ W := by
    intro hcW
    obtain ⟨i, hi⟩ := hSne
    exact hno i hi c hcW (hc i hi)
  have hun : ∀ i ∈ S, ¬ ∃ d, π i = some d ∧ d ∈ A i := by
    intro i hi ⟨d, hd, hdA⟩
    have hdW : d ∈ W := hv.2.1 i d hd
    exact hno i hi d hdW hdA
  have hS_not_all_none : ∃ i ∈ S, π i ≠ none := by
    by_contra hall
    push Not at hall
    have hsub : S ⊆ Finset.univ.filter fun i => π i = none := by
      intro i hi
      simp [hall i hi]
    have hle := Finset.card_le_card hsub
    rw [hv.2.2.2] at hle
    have : (k + 1) * S.card ≤ (k + 1) * (n / (k + 1)) := Nat.mul_le_mul_left (k + 1) hle
    have : (k + 1) * (n / (k + 1)) ≤ n := Nat.mul_div_le n (k + 1)
    omega
  obtain ⟨i₀, hi₀, hni₀⟩ := hS_not_all_none
  obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.1 hni₀
  have hc₀W : c₀ ∈ W := hv.2.1 i₀ c₀ hc₀
  obtain ⟨π', hv', hsc⟩ := droop_monroe_exchange A k W π hv c₀ c hc₀W hcW S hc hun
  have hopt_le := hopt _ π' hv'
  set R := Finset.univ.filter fun i => π i = some c₀ with hR
  have hR_le_ceil : R.card ≤ (n + k) / (k + 1) := (hv.2.2.1 c₀ hc₀W).2
  have hfloor_lt : n / (k + 1) < S.card := by
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos k), mul_comm]
    exact hS
  have hceil_le_S : (n + k) / (k + 1) ≤ S.card := by
    have h1 : n + k ≤ n + (k + 1) := by omega
    have h2 : (n + k) / (k + 1) ≤ (n + (k + 1)) / (k + 1) := Nat.div_le_div_right h1
    have h3 : (n + (k + 1)) / (k + 1) = n / (k + 1) + 1 := Nat.add_div_right n (Nat.succ_pos k)
    rw [h3] at h2
    omega
  have hR_le_S : R.card ≤ S.card := hR_le_ceil.trans hceil_le_S
  have hmin : min R.card S.card = R.card := min_eq_left hR_le_S
  rw [hmin] at hsc
  have hsplit : R.card = (R.filter fun i => i ∉ S).card + (R.filter fun i => i ∈ S).card := by
    have := (Finset.card_filter_add_card_filter_not (s := R) (p := fun i => i ∈ S)).symm
    rw [add_comm] at this
    exact this
  have hin : i₀ ∈ R.filter fun i => i ∈ S := by
    simp [hR, hc₀, hi₀]
  have hpos : 0 < (R.filter fun i => i ∈ S).card := Finset.card_pos.2 ⟨i₀, hin⟩
  omega
