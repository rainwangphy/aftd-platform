import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# alpha_lexical_second_cell_lt_first

Topic: combinatorics   Node: 9fb95e95cb19

Provenance: helper lemma. Elementary lexical cell bound for OP-392, arXiv:2610.24758.

The second cell of any lexical sequence of length at least two is strictly smaller than its first cell.
-/

theorem alpha_lexical_second_cell_lt_first (a : List ℕ)
 (ha : alpha_is_lexical a) (hlen : 2 ≤ a.length) : a.getD 1 0 < a.getD 0 0 := by  classical
  have hle := alpha_lexical_first_negative_step_exists_cell_le_first a ha 1 (by omega)
  by_contra hnot
  have heq : a.getD 1 0 = a.getD 0 0 := by omega
  let s : Finset ℕ := (Finset.range a.length).filter (fun k => a.getD k 0 = a.getD 0 0)
  have h1s : 1 ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, heq⟩
  have hs : s.Nonempty := ⟨1, h1s⟩
  let r := s.max' hs
  have hrs : r ∈ s := Finset.max'_mem s hs
  have hrlen : r < a.length := Finset.mem_range.mp (Finset.mem_filter.mp hrs).1
  have hrval : a.getD r 0 = a.getD 0 0 := (Finset.mem_filter.mp hrs).2
  have hrpos : 0 < r := by
    have := Finset.le_max' s 1 h1s
    omega
  have hfirstpos : 0 < a.getD 0 0 :=
    alpha_lexical_first_negative_step_exists_cell_pos a ha 0 (by omega)
  have hnext : a.getD (r + 1) 0 < a.getD 0 0 := by
    by_cases hrl : r + 1 < a.length
    · have hnextle := alpha_lexical_first_negative_step_exists_cell_le_first a ha (r+1) hrl
      have hne : a.getD (r+1) 0 ≠ a.getD 0 0 := by
        intro h
        have hmem : r+1 ∈ s := by
          simp only [s, Finset.mem_filter, Finset.mem_range]
          exact ⟨hrl, h⟩
        have := Finset.le_max' s (r+1) hmem
        omega
      omega
    · have hz : a.getD (r+1) 0 = 0 := List.getD_eq_default _ _ (by omega)
      omega
  have h0 : a.getD 0 0 = (a.drop r).getD 0 0 := by
    rw [alpha_lexical_first_negative_step_exists_getD_drop_zero, hrval]
  have h1 : (a.drop r).getD 1 0 < a.getD 1 0 := by
    rw [alpha_lexical_first_negative_step_exists_getD_drop, heq]
    exact hnext
  have hlt : alpha_lexical_lt a (a.drop r) :=
    alpha_lexical_first_negative_step_exists_lt_of_second_cell_gt a (a.drop r) h0 h1
      (lt_of_lt_of_le (by omega : 1 < a.length) (le_max_left _ _))
  have hback : alpha_lexical_lt (a.drop r) a := ha.2.2 r hrlen hrpos
  have hirr := alpha_lexical_first_negative_step_exists_lt_trans a (a.drop r) a hlt hback
  rcases hirr with ⟨j, _, _, hj⟩
  exact (lt_irrefl _ hj)
