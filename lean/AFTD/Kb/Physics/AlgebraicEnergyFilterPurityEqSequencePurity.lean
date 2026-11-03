import AFTD.Prelude
import AFTD.Kb.Physics.AlgebraicEnergyFilterPurity
import AFTD.Kb.Physics.EnergyFilterSequencePurity

/-!
# algebraic_energy_filter_purity_eq_sequence_purity

Topic: statistical_mechanics   Node: 374731075c78

Provenance: helper lemma. arXiv:2405.02158, Energy-Filtered Pure States as Thermal State Surrogates

For every natural number k and real s, the algebraic energy-filtered bipartite Renyi-2 purity algebraic_energy_filter_purity k s on 4k spins equals the sequence purity energy_filter_sequence_purity a k for the sequence filter a(j) = (1 + 2 * |j|)^(-s).
-/

lemma algebraic_energy_filter_purity_eq_sequence_purity_sum_bool_to_real
    (k : ℕ) (s : Fin (2 * k) → Bool) :
    (∑ j : Fin (2 * k), (if s j = true then (1 : ℝ) else -1)) =
      2 * (∑ j : Fin (2 * k), (if s j = true then (1 : ℝ) else 0)) - 2 * (k : ℝ) := by
  have h (j : Fin (2 * k)) : (if s j = true then (1 : ℝ) else -1) = 2 * (if s j = true then (1 : ℝ) else 0) - 1 := by
    cases s j <;> norm_num
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma algebraic_energy_filter_purity_eq_sequence_purity_sum_bool_cast
    (k : ℕ) (s : Fin (2 * k) → Bool) :
    (∑ j : Fin (2 * k), (if s j = true then (1 : ℝ) else 0)) =
      ((∑ j : Fin (2 * k), if s j = true then (1 : ℤ) else 0) : ℝ) := by
  push_cast
  rfl

lemma algebraic_energy_filter_purity_eq_sequence_purity_abs_eq
    (k : ℕ) (sA sB : Fin (2 * k) → Bool) :
    |(∑ j, if sA j = true then (1 : ℝ) else -1) + ∑ j, if sB j = true then (1 : ℝ) else -1| =
      2 * |((((2 * (k : ℤ) - ∑ j, if sA j = true then (1 : ℤ) else 0) - ∑ j, if sB j = true then (1 : ℤ) else 0) : ℤ) : ℝ)| := by
  rw [algebraic_energy_filter_purity_eq_sequence_purity_sum_bool_to_real k sA,
      algebraic_energy_filter_purity_eq_sequence_purity_sum_bool_to_real k sB]
  rw [algebraic_energy_filter_purity_eq_sequence_purity_sum_bool_cast k sA,
      algebraic_energy_filter_purity_eq_sequence_purity_sum_bool_cast k sB]
  have : (2 * ((∑ j, if sA j = true then (1 : ℤ) else 0) : ℝ) - 2 * (k : ℝ)) +
         (2 * ((∑ j, if sB j = true then (1 : ℤ) else 0) : ℝ) - 2 * (k : ℝ)) =
         (-2) * ((((2 * (k : ℤ) - ∑ j, if sA j = true then (1 : ℤ) else 0) - ∑ j, if sB j = true then (1 : ℤ) else 0) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [this, abs_mul]
  norm_num

/-- The algebraic energy-filter purity on 4k spins equals the sequence purity for a(j) = (1 + 2|j|)^(-s). -/
theorem algebraic_energy_filter_purity_eq_sequence_purity (k : ℕ) (s : ℝ) :
    algebraic_energy_filter_purity k s =
      energy_filter_sequence_purity (fun j => (1 + 2 * |(j : ℝ)|) ^ (-s)) k := by
  unfold algebraic_energy_filter_purity energy_filter_sequence_purity
  dsimp only
  have hM : (fun sA sB : Fin (2 * k) → Bool =>
      (1 + |(∑ j, if sA j = true then (1 : ℝ) else -1) + ∑ j, if sB j = true then (1 : ℝ) else -1|) ^ (-s)) =
    (fun sA sB : Fin (2 * k) → Bool =>
      (1 + 2 * |((((2 * (k : ℤ) - ∑ j, if sA j = true then (1 : ℤ) else 0) - ∑ j, if sB j = true then (1 : ℤ) else 0) : ℤ) : ℝ)|) ^ (-s)) := by
    ext sA sB
    rw [algebraic_energy_filter_purity_eq_sequence_purity_abs_eq k sA sB]
  rw [hM]
