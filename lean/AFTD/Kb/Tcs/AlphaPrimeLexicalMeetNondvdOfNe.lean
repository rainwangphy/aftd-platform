import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalMeetSumLtOfNeOfSumEq
import AFTD.Kb.Tcs.AlphaLexicalMeetIsLexical
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalMeet

/-!
# alpha_prime_lexical_meet_nondvd_of_ne

Topic: combinatorics   Node: 481320c7f166

Provenance: helper lemma. Proper-meet helpers for the published lexical adjacency criterion, arXiv:0810.5205v2, Theorem3.1 and Corollary3.3, supporting the run-length route for OP-392. These routine reductions do not prove the adjacency theorem and no research advance is claimed.

For any distinct lexical sequences of the same prime degree, the meet degree is a proper nontrivial value and does not divide the ambient prime degree.
-/

theorem alpha_prime_lexical_meet_nondvd_of_ne
    (p : ℕ) (hp : p.Prime) (a b : List ℕ)
    (ha : alpha_is_lexical a) (hb : alpha_is_lexical b)
    (hsa : a.sum + 1 = p) (hsb : b.sum + 1 = p) (hne : a ≠ b) :
    ¬ ((alpha_lexical_meet a b).sum + 1) ∣ p := by
  have hf := alpha_lexical_meet_is_lexical a b ha hb
  have hpos : 0 < (alpha_lexical_meet a b).sum := by
    cases he : alpha_lexical_meet a b with
    | nil => exact False.elim (hf.1 he)
    | cons x xs =>
        have hx := hf.2.1 x (by rw [he]; simp)
        simp only [he, List.sum_cons]
        omega
  have hlt := alpha_lexical_meet_sum_lt_of_ne_of_sum_eq a b ha.2.1 hb.2.1 hne
    (by omega)
  intro hd
  rcases hp.eq_one_or_self_of_dvd _ hd with he | he <;> omega
