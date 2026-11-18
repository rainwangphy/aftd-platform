import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaEvenSplitEarlySuffixLtOfLexicalPrefix
import AFTD.Kb.Tcs.AlphaSignedPrefixOfLexicalInterval
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists

/-!
# alpha_even_split_blocking_suffix_repeats_prefix

Topic: combinatorics   Node: 17cbc73bbd74

Provenance: helper lemma. Helper for the divisor-prefix route to OP-392, arXiv:2610.24758; alternating order as in arXiv:0810.5205.

For an even-indexed split after a lexical prefix of a lexical sequence, every suffix obstructing lexicality starts after the inserted cell and begins with a copy of the whole original preceding prefix.
-/

theorem alpha_even_split_blocking_suffix_repeats_prefix (a : List ℕ) (i k : ℕ) (ha : alpha_is_lexical a) (hi0 : 0 < i) (hi : i < a.length) (he : i % 2 = 0) (hc : 1 < a.getD i 0) (hp : alpha_is_lexical (a.take i)) : let c := a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1); 0 < k → k < c.length → ¬ alpha_lexical_lt (c.drop k) c → i + 1 < k ∧ (c.drop k).take i = a.take i := by
  dsimp only
  intro hk0 hklen hblock
  have hearly := alpha_even_split_early_suffix_lt_of_lexical_prefix a i ha hi0 hi he hc hp
  have hgt : i + 1 < k := by
    by_contra H
    exact hblock (hearly k hk0 hklen (by omega))
  refine ⟨hgt, ?_⟩
  have hk2 : i + 2 ≤ k := by omega
  have hclen : (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).length = a.length + 1 := by
    rw [List.length_append, List.length_append, List.length_take, List.length_drop]
    simp; omega
  have hdrop : (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k = a.drop (k - 1) := by
    rw [List.drop_append]
    rw [List.drop_append]
    have h1 : (a.take i).length = i := by rw [List.length_take]; omega
    have h2 : (a.take i ++ [a.getD i 0 - 1, 1]).length = i + 2 := by
      rw [List.length_append, h1]; simp
    rw [h1, h2]
    have hd1 : List.drop k (a.take i) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.nil_append]
    have hd2 : List.drop (k - i) [a.getD i 0 - 1, 1] = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [hd2, List.nil_append]
    rw [List.drop_drop]
    congr 1
    omega
  have hctake : (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).take i = a.take i := by
    rw [List.take_append_of_le_length]
    · rw [List.take_append_of_le_length]
      · rw [List.take_of_length_le (by rw [List.length_take]; omega)]
      · rw [List.length_take]; omega
    · rw [List.length_append, List.length_take]; omega
  have hgetD_ca : ∀ j < i, (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).getD j 0 = a.getD j 0 := by
    intro j hj
    rw [List.getD_append (a.take i ++ [a.getD i 0 - 1, 1]) (a.drop (i + 1)) 0 j
      (by rw [List.length_append, List.length_take]; simp; omega)]
    rw [List.getD_append (a.take i) ([a.getD i 0 - 1, 1]) 0 j (by rw [List.length_take]; omega)]
    rw [List.getD_eq_getElem _ 0 (by rw [List.length_take]; omega),
        List.getD_eq_getElem _ 0 (by omega)]
    rw [List.getElem_take]
  have hac : ∀ j < i, alpha_signed_cell a j = alpha_signed_cell (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)) j := by
    intro j hj
    simp only [alpha_signed_cell]
    rw [hgetD_ca j hj]
  have hu : alpha_lexical_lt ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k) a := by
    rw [hdrop]
    exact ha.2.2 (k - 1) (by omega) (by omega)
  have hpref := alpha_signed_prefix_of_lexical_interval ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k) a (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)) i (by rw [hclen]; omega) hu hblock hac
  have hcd_eq : ∀ j < i, ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k).getD j 0 = a.getD j 0 := by
    intro j hj
    have h := hpref j hj
    unfold alpha_signed_cell at h
    split_ifs at h
    · exact Nat.cast_injective h
    · exact Nat.cast_injective (neg_inj.mp h)
  have hlen_ge : i ≤ ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k).length := by
    have hposa : 0 < a.getD (i - 1) 0 := alpha_lexical_first_negative_step_exists_cell_pos a ha (i - 1) (by omega)
    have hpos := hcd_eq (i - 1) (by omega)
    have hpos' : 0 < ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k).getD (i - 1) 0 := by
      rw [hpos]; exact hposa
    have hlt : i - 1 < ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k).length := by
      by_contra H
      rw [not_lt] at H
      have hz : ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k).getD (i - 1) 0 = 0 :=
        List.getD_eq_default _ _ H
      rw [hz] at hpos'
      omega
    omega
  apply List.ext_getElem
  · rw [List.length_take, List.length_take]; omega
  · intro j hj1 hj2
    rw [List.getElem_take, List.getElem_take]
    have hu1 : j < ((a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).drop k).length := by
      rw [List.length_take] at hj1; omega
    have ha1 : j < a.length := by rw [List.length_take] at hj2; omega
    rw [← List.getD_eq_getElem _ 0 hu1, ← List.getD_eq_getElem _ 0 ha1]
    exact hcd_eq j (by rw [List.length_take] at hj1; omega)
