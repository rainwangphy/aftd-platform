import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalMeet

/-!
# alpha_lexical_meet_sum_lt_of_ne_of_sum_eq

Topic: combinatorics   Node: 4e4c90cb7595

Provenance: helper lemma. Proper-meet helpers for the published lexical adjacency criterion, arXiv:0810.5205v2, Theorem3.1 and Corollary3.3, supporting the run-length route for OP-392. These routine reductions do not prove the adjacency theorem and no research advance is claimed.

The common lexical meet of two distinct positive integer sequences of equal sum has strictly smaller sum than either input.
-/

theorem alpha_lexical_meet_sum_lt_of_ne_of_sum_eq
    (a b : List ℕ) (hapos : ∀ v ∈ a, 0 < v) (hbpos : ∀ v ∈ b, 0 < v)
    (hne : a ≠ b) (hsum : a.sum = b.sum) :
    (alpha_lexical_meet a b).sum < a.sum := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => exact False.elim (hne rfl)
      | cons y ys =>
          have hy := hbpos y (by simp)
          simp only [List.sum_nil, List.sum_cons] at hsum
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          have hx := hapos x (by simp)
          simp only [List.sum_nil, List.sum_cons] at hsum
          omega
      | cons y ys =>
          by_cases hxy : x = y
          · subst y
            have htail : xs ≠ ys := by
              intro he
              apply hne
              rw [he]
            have hstail : xs.sum = ys.sum := by
              simp only [List.sum_cons] at hsum
              omega
            have hh := ih ys (fun v hv => hapos v (by simp [hv]))
              (fun v hv => hbpos v (by simp [hv])) htail hstail
            simp only [alpha_lexical_meet, ↓reduceIte, List.sum_cons]
            omega
          · simp only [alpha_lexical_meet, if_neg hxy, List.sum_cons, List.sum_nil]
            simp only [List.sum_cons] at hsum
            rcases lt_or_gt_of_ne hxy with hh | hh
            · rw [Nat.min_eq_left hh.le]
              omega
            · rw [Nat.min_eq_right hh.le]
              omega
