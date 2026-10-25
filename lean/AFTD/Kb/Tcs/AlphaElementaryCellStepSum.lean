import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaElementaryCellStep

/-!
# alpha_elementary_cell_step_sum

Topic: combinatorics   Node: 520ce4c4fe5d

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Elementary splitting and conjugation preserve the degree.
-/

lemma alpha_elementary_cell_step_sum_aux (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l.sum = (l.take i).sum + l.getD i 0 + (l.drop (i + 1)).sum := by
  have hd : l.drop i = l.getD i 0 :: l.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem l 0 h]
  calc l.sum = (l.take i ++ l.drop i).sum := by rw [List.take_append_drop]
    _ = (l.take i).sum + (l.drop i).sum := List.sum_append
    _ = (l.take i).sum + (l.getD i 0 + (l.drop (i + 1)).sum) := by rw [hd, List.sum_cons]
    _ = (l.take i).sum + l.getD i 0 + (l.drop (i + 1)).sum := by rw [Nat.add_assoc]

theorem alpha_elementary_cell_step_sum (a b : List ℕ) (i : ℕ) (h : alpha_elementary_cell_step a b i) : b.sum = a.sum := by
  rcases h with ⟨hi, h | h⟩
  · rcases h with ⟨hgt, hb⟩
    have ha := alpha_elementary_cell_step_sum_aux a i hi
    rw [hb]
    simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    omega
  · rcases h with ⟨hpos, hget, hb⟩
    have ha := alpha_elementary_cell_step_sum_aux a i hi
    have hlt : i - 1 < a.length := by omega
    have htake : a.take i = a.take (i - 1) ++ [a.getD (i - 1) 0] := by
      rw [List.getD_eq_getElem a 0 hlt, List.take_append_getElem hlt,
        Nat.sub_add_cancel (by omega : 1 ≤ i)]
    have hsum_take : (a.take i).sum = (a.take (i - 1)).sum + a.getD (i - 1) 0 := by
      rw [htake, List.sum_append, List.sum_singleton]
    rw [hb]
    simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    omega
