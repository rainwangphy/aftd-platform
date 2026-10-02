import AFTD.Prelude
import AFTD.Kb.NumberTheory.RangeCardFilterDvd

/-!
# fin_card_filter_dvd

Topic: elementary_number_theory   Node: 03fe904e6cf7

For m > 0, exactly (k + m - 1)/m of the positions 0, ..., k-1 are multiples of m.
-/

theorem fin_card_filter_dvd (m k : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun j : Fin k => m ∣ (j : ℕ)).card = (k + m - 1) / m := by
  rw [← range_card_filter_dvd m k hm, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun j => if m ∣ j then 1 else 0)]
