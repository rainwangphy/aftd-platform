import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFourCodeCardAchievable
import AFTD.Kb.Tcs.TwoFourCodeMaxCard
import AFTD.Kb.Tcs.IsTwoFourCode

/-!
# two_four_code_max_card_ge

Topic: information   Node: b9da375d8af0

Provenance: helper lemma. step towards op_491_threshold_le

For every $q \ge 2$ and every $n$, $1 + \binom{n}{2} \le A_q(n,\{2,4\})$, i.e. the extremal code of the previous lemma is counted by the supremum defining $A_q(n,\{2,4\})$. This is equation (1) of arXiv:2610.30613 and holds with no threshold on $n$.
-/

/-- Lower bound A_q(n,{2,4}) &ge; 1 + C(n,2), for every length n and every q &ge; 2. -/
theorem two_four_code_max_card_ge (q n : ℕ) (hq : 2 ≤ q) :
    1 + n.choose 2 ≤ two_four_code_max_card q n := by
  unfold two_four_code_max_card
  apply le_csSup
  · refine ⟨Fintype.card (Fin n → Fin q), ?_⟩
    rintro k ⟨s, rfl, -⟩
    exact Finset.card_le_univ s
  · obtain ⟨C, hcard, hcode⟩ := two_four_code_card_achievable q n hq
    exact ⟨C, hcard, hcode⟩
