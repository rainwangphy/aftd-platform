import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterCenteredRowSum
import AFTD.Kb.Physics.EnergyFilterCenteredWeightAtRow
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# energy_filter_centered_binomial_tsum4_to_row

Topic: statistical_mechanics   Node: beaaaefb18e2

Provenance: helper lemma. OP-892: binomial-row specialization of the exact trace reindexing.

For any real integer sequence and k, the four-index centered-binomial weighted cycle sum equals the original fourfold binomial row sum divided by the fourth power of the central coefficient.
-/

theorem energy_filter_centered_binomial_tsum4_to_row (k : ℕ) (a : ℤ → ℝ) :
    (∑' q : ℤ × ℤ × ℤ × ℤ,
      energy_filter_centered_binomial_weight k q.1 *
      energy_filter_centered_binomial_weight k q.2.1 *
      energy_filter_centered_binomial_weight k q.2.2.1 *
      energy_filter_centered_binomial_weight k q.2.2.2 *
        (a (-q.1-q.2.1) * a (-q.2.1-q.2.2.1) *
         a (-q.2.2.1-q.2.2.2) * a (-q.2.2.2-q.1))) =
    (∑ p ∈ Finset.range (2 * k + 1), ∑ q ∈ Finset.range (2 * k + 1),
     ∑ r ∈ Finset.range (2 * k + 1), ∑ s ∈ Finset.range (2 * k + 1),
      (Nat.choose (2 * k) p : ℝ) * (Nat.choose (2 * k) q : ℝ) *
        (Nat.choose (2 * k) r : ℝ) * (Nat.choose (2 * k) s : ℝ) *
        (a (2 * (k : ℤ) - (p : ℤ) - (q : ℤ)) * a (2 * (k : ℤ) - (q : ℤ) - (r : ℤ)) *
         a (2 * (k : ℤ) - (r : ℤ) - (s : ℤ)) * a (2 * (k : ℤ) - (s : ℤ) - (p : ℤ)))) /
      (Nat.choose (2 * k) k : ℝ) ^ 4 := by
  classical
  let S : Finset ℤ := Finset.Icc (-(k:ℤ)) (k:ℤ)
  let F : ℤ × ℤ × ℤ × ℤ → ℝ := fun q =>
    energy_filter_centered_binomial_weight k q.1 *
      energy_filter_centered_binomial_weight k q.2.1 *
      energy_filter_centered_binomial_weight k q.2.2.1 *
      energy_filter_centered_binomial_weight k q.2.2.2 *
      (a (-q.1-q.2.1) * a (-q.2.1-q.2.2.1) *
       a (-q.2.2.1-q.2.2.2) * a (-q.2.2.2-q.1))
  have hz (t : ℤ) (ht : t ∉ S) : energy_filter_centered_binomial_weight k t = 0 := by
    have h : ¬ (-(k:ℤ) ≤ t ∧ t ≤ (k:ℤ)) := by simpa [S] using ht
    simp [energy_filter_centered_binomial_weight, h]
  change (∑' q, F q) = _
  rw [tsum_eq_sum (s := S.product (S.product (S.product S)))]
  · have hprod : (∑ x ∈ S.product (S.product (S.product S)), F x) =
        ∑ p ∈ S, ∑ x ∈ S.product (S.product S), F (p,x) :=
      Finset.sum_product S (S.product (S.product S)) F
    rw [hprod]
    have hprod2 (p : ℤ) : (∑ x ∈ S.product (S.product S), F (p,x)) =
        ∑ q ∈ S, ∑ x ∈ S.product S, F (p,q,x) :=
      Finset.sum_product S (S.product S) (fun x => F (p,x))
    simp_rw [hprod2]
    have hprod3 (p q : ℤ) : (∑ x ∈ S.product S, F (p,q,x)) =
        ∑ r ∈ S, ∑ s ∈ S, F (p,q,r,s) :=
      Finset.sum_product S S (fun x => F (p,q,x))
    simp_rw [hprod3]
    simp_rw [show ∀ f : ℤ → ℝ, (∑ t ∈ S, f t) =
      ∑ j ∈ Finset.range (2*k+1), f ((j:ℤ)-(k:ℤ)) from energy_filter_centered_row_sum k]
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [F]
    have hp' := Finset.mem_range.mp hp
    have hq' := Finset.mem_range.mp hq
    have hr' := Finset.mem_range.mp hr
    have hs' := Finset.mem_range.mp hs
    rw [energy_filter_centered_weight_at_row k p hp', energy_filter_centered_weight_at_row k q hq',
      energy_filter_centered_weight_at_row k r hr', energy_filter_centered_weight_at_row k s hs']
    have h1 : -((p:ℤ)-(k:ℤ))-((q:ℤ)-(k:ℤ)) = 2*(k:ℤ)-(p:ℤ)-(q:ℤ) := by ring
    have h2 : -((q:ℤ)-(k:ℤ))-((r:ℤ)-(k:ℤ)) = 2*(k:ℤ)-(q:ℤ)-(r:ℤ) := by ring
    have h3 : -((r:ℤ)-(k:ℤ))-((s:ℤ)-(k:ℤ)) = 2*(k:ℤ)-(r:ℤ)-(s:ℤ) := by ring
    have h4 : -((s:ℤ)-(k:ℤ))-((p:ℤ)-(k:ℤ)) = 2*(k:ℤ)-(s:ℤ)-(p:ℤ) := by ring
    rw [h1,h2,h3,h4]
    ring
  · intro q hq
    have hn : q.1 ∉ S ∨ q.2.1 ∉ S ∨ q.2.2.1 ∉ S ∨ q.2.2.2 ∉ S := by
      by_contra hn
      have h1 : q.1 ∈ S := by tauto
      have h2 : q.2.1 ∈ S := by tauto
      have h3 : q.2.2.1 ∈ S := by tauto
      have h4 : q.2.2.2 ∈ S := by tauto
      apply hq
      exact Finset.mem_product.mpr ⟨h1, Finset.mem_product.mpr ⟨h2, Finset.mem_product.mpr ⟨h3,h4⟩⟩⟩
    rcases hn with h1 | h2 | h3 | h4
    · simp [F, hz _ h1]
    · simp [F, hz _ h2]
    · simp [F, hz _ h3]
    · simp [F, hz _ h4]
