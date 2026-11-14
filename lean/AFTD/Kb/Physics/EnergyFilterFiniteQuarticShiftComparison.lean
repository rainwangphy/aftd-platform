import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFiniteCubeProductCs

/-!
# energy_filter_finite_quartic_shift_comparison

Topic: statistical_mechanics   Node: 1c147039e8b5

Provenance: helper lemma. OP-892: shifted binomial kernel comparison.

For finite real sequences, if a, c, d lie between zero and one, the squared difference between the sum of abcd and the sum of a⁴ is bounded by three times the sum of a² times the sum of the three squared differences b−a, c−a, and d−a.
-/

theorem energy_filter_finite_quartic_shift_comparison {ι : Type*} (s : Finset ι)
    (a b c d : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ 1)
    (hd : ∀ i ∈ s, 0 ≤ d i ∧ d i ≤ 1) :
    ((∑ i ∈ s, a i * b i * c i * d i) - ∑ i ∈ s, a i ^ 4) ^ 2 ≤
      3 * (∑ i ∈ s, a i ^ 2) *
        ((∑ i ∈ s, (b i - a i) ^ 2) +
         (∑ i ∈ s, (c i - a i) ^ 2) +
         (∑ i ∈ s, (d i - a i) ^ 2)) := by
  let r : ι → ℝ := fun i =>
    (b i - a i) * c i * d i + a i * (c i - a i) * d i + a i ^ 2 * (d i - a i)
  have hr : ∀ i ∈ s, r i ^ 2 ≤ 3 *
      ((b i - a i)^2 + (c i - a i)^2 + (d i - a i)^2) := by
    intro i hi
    obtain ⟨ha0,ha1⟩ := ha i hi
    obtain ⟨hc0,hc1⟩ := hc i hi
    obtain ⟨hd0,hd1⟩ := hd i hi
    have ha2 : (a i)^2 ≤ 1 := by nlinarith [sq_nonneg (a i), mul_nonneg ha0 (sub_nonneg.mpr ha1)]
    have hc2 : (c i)^2 ≤ 1 := by nlinarith [sq_nonneg (c i), mul_nonneg hc0 (sub_nonneg.mpr hc1)]
    have hd2 : (d i)^2 ≤ 1 := by nlinarith [sq_nonneg (d i), mul_nonneg hd0 (sub_nonneg.mpr hd1)]
    have hcd : (c i * d i)^2 ≤ 1 := by nlinarith [sq_nonneg (c i), sq_nonneg (d i), mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg (d i))]
    have had : (a i * d i)^2 ≤ 1 := by nlinarith [sq_nonneg (a i), sq_nonneg (d i), mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg (d i))]
    have ha4 : (a i ^ 2)^2 ≤ 1 := by nlinarith [sq_nonneg (a i), mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg (a i))]
    have h1 : ((b i - a i) * c i * d i)^2 ≤ (b i - a i)^2 := by
      nlinarith [mul_nonneg (sq_nonneg (b i - a i)) (sub_nonneg.mpr hcd)]
    have h2 : (a i * (c i - a i) * d i)^2 ≤ (c i - a i)^2 := by
      nlinarith [mul_nonneg (sq_nonneg (c i - a i)) (sub_nonneg.mpr had)]
    have h3 : (a i ^ 2 * (d i - a i))^2 ≤ (d i - a i)^2 := by
      nlinarith [mul_nonneg (sq_nonneg (d i - a i)) (sub_nonneg.mpr ha4)]
    dsimp [r]
    nlinarith [sq_nonneg ((b i - a i) * c i * d i - a i * (c i - a i) * d i),
      sq_nonneg ((b i - a i) * c i * d i - a i ^ 2 * (d i - a i)),
      sq_nonneg (a i * (c i - a i) * d i - a i ^ 2 * (d i - a i))]
  have hsum : (∑ i ∈ s, r i ^ 2) ≤ 3 *
      ((∑ i ∈ s, (b i-a i)^2) + (∑ i ∈ s, (c i-a i)^2) + (∑ i ∈ s, (d i-a i)^2)) := by
    calc
      _ ≤ ∑ i ∈ s, 3 * ((b i-a i)^2 + (c i-a i)^2 + (d i-a i)^2) := Finset.sum_le_sum hr
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s a r
  have heq : (∑ i ∈ s, a i * r i) =
      (∑ i ∈ s, a i * b i * c i * d i) - ∑ i ∈ s, a i ^ 4 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [r]
    ring
  rw [heq] at hcs
  calc
    _ ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, r i ^ 2) := hcs
    _ ≤ (∑ i ∈ s, a i ^ 2) * (3 * ((∑ i ∈ s, (b i-a i)^2) + (∑ i ∈ s, (c i-a i)^2) + (∑ i ∈ s, (d i-a i)^2))) :=
      mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg fun i hi => sq_nonneg _)
    _ = _ := by ring
