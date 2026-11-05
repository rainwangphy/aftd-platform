import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsExAnteProportionalChores
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_ex_ante_proportional_of_equal_marginal

Topic: fair_division   Node: 3e36c1b2097f

Provenance: helper lemma. arXiv:2609.35280

Every equal-marginal lottery over complete chore allocations is ex-ante proportional for any profile of chore costs.
-/

/-- An equal-marginal chore lottery is ex-ante proportional. -/
theorem is_ex_ante_proportional_of_equal_marginal {m n : ℕ} (c : Fin n → Fin m → ℝ)
    (p : (Fin m → Fin n) → ℝ) (hp : is_equal_marginal_lottery p) :
    is_ex_ante_proportional_chores c p := by
  intro i
  have h1 (σ : Fin m → Fin n) : additive_valuation (c i) (bundle_of σ i) = ∑ j, if σ j = i then c i j else 0 := by
    dsimp [additive_valuation, bundle_of]
    rw [Finset.sum_filter]
  simp_rw [h1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 (j : Fin m) : (∑ σ, p σ * if σ j = i then c i j else 0) = c i j / ↑n := by
    have h3 : (∑ σ, p σ * if σ j = i then c i j else 0) = (∑ σ, (if σ j = i then p σ else 0)) * c i j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> ring
    rw [h3, hp j i]
    ring
  simp_rw [h2]
  rw [← Finset.sum_div]
