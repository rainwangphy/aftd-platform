import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexListAppendComm
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRhoStar
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderUpdateCentre
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_gamma_swap_two

Topic: combinatorial_games   Node: 7aa41c91dd58

Provenance: helper lemma. step towards spider_blocked_incoming_one_inward

The Grundy value of a two-legged spider state is invariant under swapping the two legs in the list.
-/

/-- The Grundy value of a two-legged spider state is invariant under swapping the two legs in the list. -/
theorem spider_gamma_swap_two (fuel : ℕ) (s : CentreStatus) (A B : ℕ × SpiderLegEnd) :
    spider_gamma fuel s [A, B] = spider_gamma fuel s [B, A] := by
  cases fuel with
  | zero => rfl
  | succ f =>
    cases s with
    | free =>
      dsimp [spider_gamma]
      rw [Nat.zero_xor, Nat.zero_xor, Nat.xor_comm]
    | _ =>
      dsimp [spider_gamma]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      dsimp [List.eraseIdx]
      rw [nat_mex_list_append_comm]
