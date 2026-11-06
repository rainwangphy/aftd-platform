import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# two_agent_balanced_symmetric_swap_lottery

Topic: fair_division   Node: 6a9aa6552f2c

Provenance: helper lemma. Symmetric two-allocation lottery reduction for the equal-marginal problem in IN-570.

If both bundles of a two-way partition cost at most alpha times the maximin share of each agent, the equal mixture of that allocation and its swap is an equal-marginal lottery whose support is alpha-MMS.
-/

theorem two_agent_balanced_symmetric_swap_lottery
    (m : ℕ) (α : ℝ) (c : Fin 2 → Fin m → ℝ) (S : Finset (Fin m))
    (hS : ∀ i, additive_valuation (c i) S ≤ α * chore_maximin_share 2 (c i))
    (hSc : ∀ i, additive_valuation (c i) (Finset.univ \ S) ≤
      α * chore_maximin_share 2 (c i)) :
    ∃ p ∈ stdSimplex ℝ (Fin m → Fin 2),
      is_equal_marginal_lottery p ∧ is_ex_post_alpha_mms_chores α c p := by
  classical
  let σ : Fin m → Fin 2 := fun g => if g ∈ S then 0 else 1
  let τ : Fin m → Fin 2 := fun g => if g ∈ S then 1 else 0
  let p : (Fin m → Fin 2) → ℝ := fun t =>
    (if t = σ then 1 / 2 else 0) + (if t = τ then 1 / 2 else 0)
  have bσ0 : bundle_of σ 0 = S := by
    ext g
    simp [bundle_of, σ]
  have bσ1 : bundle_of σ 1 = Finset.univ \ S := by
    ext g
    simp [bundle_of, σ]
  have bτ0 : bundle_of τ 0 = Finset.univ \ S := by
    ext g
    simp [bundle_of, τ]
  have bτ1 : bundle_of τ 1 = S := by
    ext g
    simp [bundle_of, τ]
  refine ⟨p, ?_, ?_, ?_⟩
  · constructor
    · intro t
      dsimp [p]
      positivity
    · dsimp [p]
      rw [Finset.sum_add_distrib]
      simp <;> norm_num
  · intro g i
    change (∑ t : Fin m → Fin 2, if t g = i then p t else 0) = 1 / (2 : ℝ)
    have hστ : σ ≠ τ := by
      intro h
      have hv := congrFun h g
      by_cases hg : g ∈ S <;> simp [σ, τ, hg] at hv
    have hexpand (t : Fin m → Fin 2) :
        (if t g = i then p t else 0) =
          (if t = σ then (if σ g = i then (1 / 2 : ℝ) else 0) else 0) +
          (if t = τ then (if τ g = i then (1 / 2 : ℝ) else 0) else 0) := by
      by_cases hσ : t = σ
      · subst t
        simp [p, hστ]
      · by_cases hτ : t = τ
        · subst t
          simp [p, Ne.symm hστ]
        · simp [p, hσ, hτ]
    simp only [hexpand, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    fin_cases i <;> by_cases hg : g ∈ S <;> simp [σ, τ, hg]
  · intro t hp i
    change additive_valuation (c i) (bundle_of t i) ≤ α * chore_maximin_share 2 (c i)
    have ht : t = σ ∨ t = τ := by
      by_contra hh
      push_neg at hh
      simp [p, hh.1, hh.2] at hp
    rcases ht with rfl | rfl <;> fin_cases i
    · simpa [bσ0] using hS 0
    · simpa [bσ1] using hSc 1
    · simpa [bτ0] using hSc 0
    · simpa [bτ1] using hS 1
