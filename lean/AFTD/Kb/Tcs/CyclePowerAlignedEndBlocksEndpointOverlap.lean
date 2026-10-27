import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEndBlocks
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_aligned_end_blocks_endpoint_overlap

Topic: combinatorics   Node: f7a9f75f56ea

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

For nested aligned end-block widths, every class through the last point of a different old class intersects the translated new class one full arc later.
-/

open Finset

theorem cycle_power_aligned_end_blocks_endpoint_overlap
    (D a b p q c : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hA : 2 * a ≤ D) (hB : 2 * b ≤ D)
    (hDa : 2 * a ∣ D) (hDb : 2 * b ∣ D)
    (hchain : a = b ∨ 2 * a ∣ b ∨ 2 * b ∣ a)
    (hp : a ∣ p + c) (hpo : 2 * a < D → 2 * a ∣ p + c - a)
    (hq : b ∣ q + c) (hqo : 2 * b < D → 2 * b ∣ q + c - b)
    (hact : cycle_power_end_blocks D b q (p + D - 1)) (hqp : q ≠ p) :
    ∃ u, cycle_power_end_blocks D b q u ∧ cycle_power_end_blocks D a (p + D) u := by
  unfold cycle_power_end_blocks at hact ⊢
  have hRange : p < q ∧ q < p + D := by
    rcases hact with h | h <;> constructor <;> omega
  by_cases hfull : D = 2 * a
  · refine ⟨q + D - 1, Or.inr ⟨by omega, by omega⟩, ?_⟩
    by_cases hh : q + D - 1 < p + D + a
    · exact Or.inl ⟨by omega, hh⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hstrict : 2 * a < D := by omega
  rcases hact with hfirst | hlast
  · rcases hchain with heq | hab | hba
    · subst b
      have hd : 2 * a ∣ q - p := by
        have hh : 2 * a ∣ (q + c - a) - (p + c - a) :=
          dvd_sub (hqo hstrict) (hpo hstrict)
        have he : (q + c - a) - (p + c - a) = q - p := by ring
        rwa [he] at hh
      have hz : 2 * a ∣ q - p - D + 2 * a :=
        dvd_add (dvd_sub hd hDa) (dvd_refl _)
      have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt
        (by omega : 0 ≤ q - p - D + 2 * a)
        (by omega : q - p - D + 2 * a < 2 * a) hz
      omega
    · have hne : p + D - 1 ≠ q + b - 1 := by
        intro he
        have hdq : 2 * a ∣ q + c := dvd_trans hab hq
        have hdp : 2 * a ∣ p + c := by
          have hh : 2 * a ∣ (q + c - D) + b := dvd_add (dvd_sub hdq hDa) hab
          have heq : (q + c - D) + b = p + c := by omega
          rwa [heq] at hh
        have hda : 2 * a ∣ a := by
          have hh : 2 * a ∣ (p + c) - (p + c - a) := dvd_sub hdp (hpo hstrict)
          have heq : (p + c) - (p + c - a) = a := by ring
          rwa [heq] at hh
        have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt ha.le (by omega : a < 2 * a) hda
        omega
      exact ⟨p + D, Or.inl ⟨by omega, by omega⟩,
        Or.inl ⟨by omega, by omega⟩⟩
    · have hba_le : 2 * b ≤ a := Int.le_of_dvd ha hba
      have hbstrict : 2 * b < D := by omega
      have hdp : 2 * b ∣ p + c := dvd_trans hba hp
      have hz : 2 * b ∣ q - p - D + b := by
        have hh : 2 * b ∣ ((q + c - b) - (p + c) - D) + (2 * b) :=
          dvd_add (dvd_sub (dvd_sub (hqo hbstrict) hdp) hDb) (dvd_refl (2 * b))
        have heq : ((q + c - b) - (p + c) - D) + (2 * b) = q - p - D + b := by ring
        rwa [heq] at hh
      have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt
        (by omega : 0 ≤ q - p - D + b)
        (by omega : q - p - D + b < 2 * b) hz
      have hqeq : q = p + D - b := by omega
      exact ⟨q + D - 1, Or.inr ⟨by omega, by omega⟩,
        Or.inr ⟨by omega, by omega⟩⟩
  · exact ⟨p + D, Or.inr ⟨by omega, by omega⟩,
      Or.inl ⟨by omega, by omega⟩⟩
