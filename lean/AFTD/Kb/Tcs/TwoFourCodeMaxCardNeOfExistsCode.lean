import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.IsTwoFourCode

/-!
# two_four_code_max_card_ne_of_exists_code

Topic: information   Node: 88f0aff37e1d

Provenance: helper lemma. step towards op_491_threshold_in_three_candidates

If there exists a $q$-ary $\{2, 4\}$-code $C$ of length $n$ with $|C| > 1 + \binom{n}{2}$, then $A_q(n, \{2, 4\}) \ne 1 + \binom{n}{2}$.
-/

/-- If a q-ary {2, 4}-code of length n has cardinality strictly greater than 1 + binom(n, 2), then the maximum code size does not equal 1 + binom(n, 2). -/
theorem two_four_code_max_card_ne_of_exists_code (q n : ℕ) (C : Finset (Fin n → Fin q))
    (hC_code : is_two_four_code (C : Set (Fin n → Fin q)))
    (hC_card : 1 + Nat.choose n 2 < C.card) :
    two_four_code_max_card q n ≠ 1 + Nat.choose n 2 := by
  have hle : C.card ≤ two_four_code_max_card q n := by
    unfold two_four_code_max_card
    apply le_csSup
    · refine ⟨Fintype.card (Fin n → Fin q), ?_⟩
      rintro k ⟨s, rfl, -⟩
      exact Finset.card_le_univ s
    · exact ⟨C, rfl, hC_code⟩
  omega
