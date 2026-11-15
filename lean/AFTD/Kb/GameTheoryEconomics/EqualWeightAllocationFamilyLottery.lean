import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores

/-!
# equal_weight_allocation_family_lottery

Topic: fair_division   Node: 4bb3ed23e11a

Provenance: helper lemma. Conversion from an equally weighted finite allocation family to the equal-marginal lottery definitions of OP-1112.

For at least one agent, if a family of n allocations assigns each chore once to each agent across the n allocations and every family member is alpha-MMS, then the uniform mixture is an equal-marginal ex-post alpha-MMS lottery.
-/

theorem equal_weight_allocation_family_lottery (n m : ℕ) (hn : 1 ≤ n) (α : ℝ) (c : Fin n → Fin m → ℝ) (F : Fin n → Fin m → Fin n) (hbij : ∀ g, Function.Bijective (fun t => F t g)) (hsafe : ∀ t, is_alpha_mms_chores α c (F t)) : ∃ p ∈ stdSimplex ℝ (Fin m → Fin n), is_equal_marginal_lottery p ∧ is_ex_post_alpha_mms_chores α c p := by
  refine ⟨fun σ => ∑ t : Fin n, (if F t = σ then ((n:ℝ)⁻¹) else 0), ?_, ?_, ?_⟩
  · constructor
    · intro σ
      exact Finset.sum_nonneg (fun t _ => by split_ifs <;> simp)
    · rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by positivity)
  · intro j i
    have hstep : ∀ σ : Fin m → Fin n,
        (if σ j = i then (∑ t : Fin n, (if F t = σ then ((n:ℝ)⁻¹) else 0)) else 0)
        = ∑ t : Fin n, (if σ j = i then (if F t = σ then ((n:ℝ)⁻¹) else 0) else 0) := by
      intro σ
      by_cases h : σ j = i <;> simp [h]
    simp only [hstep]
    rw [Finset.sum_comm]
    have hsingle : ∀ t : Fin n,
        (∑ σ : Fin m → Fin n, (if σ j = i then (if F t = σ then ((n:ℝ)⁻¹) else 0) else 0))
        = (if (F t) j = i then ((n:ℝ)⁻¹) else 0) := by
      intro t
      rw [Finset.sum_eq_single (F t)]
      · simp
      · intro b _ hb
        rw [if_neg (Ne.symm hb)]
        simp
      · intro h; exact absurd (Finset.mem_univ (F t)) h
    rw [Finset.sum_congr rfl (fun t _ => hsingle t)]
    rw [one_div]
    let e : Fin n ≃ Fin n := Equiv.ofBijective (fun t => F t j) (hbij j)
    show (∑ t : Fin n, (fun k => (if k = i then ((n:ℝ)⁻¹) else 0)) (e t)) = (n:ℝ)⁻¹
    rw [Equiv.sum_comp e (fun k => if k = i then ((n:ℝ)⁻¹) else 0)]
    rw [Finset.sum_ite_eq']
    simp
  · intro σ hpos
    have hex : ∃ t : Fin n, F t = σ := by
      by_contra h
      simp only [not_exists] at h
      have hz : (∑ t : Fin n, (if F t = σ then ((n:ℝ)⁻¹) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        simp [h t]
      linarith
    obtain ⟨t, ht⟩ := hex
    rw [← ht]
    exact hsafe t
