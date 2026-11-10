import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicLatinMarket
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankMatching
import AFTD.Kb.GameTheoryEconomics.IsStableMatching
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair

/-!
# cyclic_latin_rank_matching_is_stable

Topic: matching_markets   Node: 26b25db65bfe

Provenance: formalization of a published result. Source: Benjamin, Converse, Krieger (1995)

For every natural number n, ordering bijection a : Fin n ≃ ZMod n, and rank r : Fin n, the matching cyclic_latin_rank_matching n a r is stable in cyclic_latin_market n a.
-/

/-- Every constant-rank matching pi_r(i) = a_r - i is stable in the opposed cyclic Latin market. -/
theorem cyclic_latin_rank_matching_is_stable (n : ℕ) (a : Fin n ≃ ZMod n) (r : Fin n) :
    is_stable_matching (cyclic_latin_market n a) (cyclic_latin_rank_matching n a r) := by
  intro m w ⟨hm, hw⟩
  dsimp [cyclic_latin_market, cyclic_latin_rank_matching] at hm hw
  have hm_eq : m + (a r - m) = a r := add_sub_cancel m (a r)
  have hw_eq : (a r - w) + w = a r := sub_add_cancel (a r) w
  rw [hm_eq, Equiv.symm_apply_apply] at hm
  rw [hw_eq, Equiv.symm_apply_apply] at hw
  omega
