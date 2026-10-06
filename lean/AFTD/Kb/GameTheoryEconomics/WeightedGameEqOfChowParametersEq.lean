import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsWeightedGame

/-!
# weighted_game_eq_of_chow_parameters_eq

Topic: general_equilibrium   Node: e439e9416cd4

Provenance: formalization of a published result. Source: Chow's theorem (1961), On the characterization of threshold functions: a threshold function is determined by its Chow parameters among all Boolean functions; stated here for simple games with threshold = quota

Chow's theorem for games: if f is weighted and g is any 0/1-valued function on coalitions with the same number of winning coalitions and, for every player, the same number of winning coalitions containing that player, then f = g.
-/

/-- Chow's theorem (1961) for games: a weighted game is determined, among all `{0,1}`-valued set functions, by its number of winning coalitions and, for each player, the number of winning coalitions containing that player. -/
theorem weighted_game_eq_of_chow_parameters_eq {n : ℕ} (f g : Finset (Fin n) → Bool)
    (hf : is_weighted_game f)
    (hW : (Finset.univ.filter fun S : Finset (Fin n) => f S = true).card
      = (Finset.univ.filter fun S : Finset (Fin n) => g S = true).card)
    (hA : ∀ i, (Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ f S = true).card
      = (Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ g S = true).card) :
    f = g := by
  obtain ⟨w, q, -, hw⟩ := hf
  have hlin : ∀ v : Finset (Fin n) → Bool,
      ∑ S, (if v S then (1:ℝ) else 0) * ∑ i ∈ S, w i
        = ∑ i, w i * ((Finset.univ.filter fun S : Finset (Fin n) => i ∈ S ∧ v S = true).card : ℝ) := by
    intro v
    have hS : ∀ S : Finset (Fin n), ∑ i ∈ S, w i = ∑ i, if i ∈ S then w i else 0 := by
      intro S; rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp_rw [hS, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hi : i ∈ S <;> by_cases hv : v S = true <;> simp [hi, hv]
  have hcnt : ∀ v : Finset (Fin n) → Bool,
      ((Finset.univ.filter fun S : Finset (Fin n) => v S = true).card : ℝ)
        = ∑ S, (if v S then (1:ℝ) else 0) := by
    intro v; rw [Finset.card_filter]; push_cast; rfl
  have hzero : ∑ S, ((if f S then (1:ℝ) else 0) - (if g S then 1 else 0)) * (∑ i ∈ S, w i - q) = 0 := by
    have e : ∀ S : Finset (Fin n), ((if f S then (1:ℝ) else 0) - (if g S then 1 else 0)) * (∑ i ∈ S, w i - q)
        = (if f S then (1:ℝ) else 0) * ∑ i ∈ S, w i - (if g S then (1:ℝ) else 0) * ∑ i ∈ S, w i
          - q * ((if f S then (1:ℝ) else 0) - (if g S then 1 else 0)) := fun S => by ring
    rw [show (∑ S, ((if f S then (1:ℝ) else 0) - (if g S then 1 else 0)) * (∑ i ∈ S, w i - q))
        = (∑ S, (if f S then (1:ℝ) else 0) * ∑ i ∈ S, w i)
          - (∑ S, (if g S then (1:ℝ) else 0) * ∑ i ∈ S, w i)
          - q * ((∑ S, (if f S then (1:ℝ) else 0)) - ∑ S, (if g S then (1:ℝ) else 0)) by
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun S _ => by rw [e S]; ring]
    rw [hlin f, hlin g, ← hcnt f, ← hcnt g, hW]
    simp_rw [hA]
    ring
  have hnn : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      0 ≤ ((if f S then (1:ℝ) else 0) - (if g S then 1 else 0)) * (∑ i ∈ S, w i - q) := by
    intro S _
    have hS := hw S
    by_cases hfS : f S = true <;> by_cases hgS : g S = true
    · simp [hfS, hgS]
    · have := hS.1 hfS
      simp [hfS, hgS]
      linarith
    · have : ∑ i ∈ S, w i < q := lt_of_not_ge fun h => hfS (hS.2 h)
      simp [hfS, hgS]
      linarith
    · simp [hfS, hgS]
  have hle : ∀ S, g S = true → f S = true := by
    intro S hgS
    by_contra hfS
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero S (Finset.mem_univ S)
    have hlt : ∑ i ∈ S, w i < q := by
      by_contra hq; exact hfS ((hw S).2 (not_lt.1 hq))
    simp only [Bool.not_eq_true] at hfS
    simp [hfS, hgS] at h0
    linarith
  have hsub : (Finset.univ.filter fun S : Finset (Fin n) => g S = true)
      ⊆ (Finset.univ.filter fun S : Finset (Fin n) => f S = true) := by
    intro S; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hle S
  have heq := Finset.eq_of_subset_of_card_le hsub hW.le
  funext S
  have hS := congrArg (fun F => S ∈ F) heq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hS
  cases hfS : f S <;> cases hgS : g S <;> simp_all
