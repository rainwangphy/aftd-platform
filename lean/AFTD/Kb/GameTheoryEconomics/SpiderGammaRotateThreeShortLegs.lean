import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaSwapTwo
import AFTD.Kb.GameTheoryEconomics.NatMexListAppendComm
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderRho
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre

/-!
# spider_gamma_rotate_three_short_legs

Topic: combinatorial_games   Node: 0cd02fb1132b

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

For any leg p, centre status and fuel, the value of (s;{p,1^in,1^out}) equals the value of (s;{1^in,1^out,p}): the leg p may be moved from the front to the back of the list.
-/

/-- Moving the front leg of {p,1^in,1^out} to the back leaves the value unchanged. -/
theorem spider_gamma_rotate_three_short_legs (fuel : ℕ) (s : CentreStatus) (p : ℕ × SpiderLegEnd) :
    spider_gamma fuel s [p, (1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)] =
      spider_gamma fuel s [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward), p] := by
  cases fuel with
  | zero => rfl
  | succ f =>
    cases s with
    | free =>
      dsimp [spider_gamma]
      rw [Nat.zero_xor, Nat.zero_xor]
      ac_rfl
    | none | incoming | outgoing =>
      dsimp [spider_gamma]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
                 List.range_one, List.filterMap_cons, List.filterMap_nil,
                 List.eraseIdx_cons_zero, List.eraseIdx_cons_succ]
      rw [nat_mex_list_append_comm, List.append_assoc]
      congr 1
      congr 1
      · simp [spider_gamma_swap_two]
      · congr 1
        · simp [spider_gamma_swap_two]
