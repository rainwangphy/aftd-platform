import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiveInducibleTournamentThreshold
import AFTD.Kb.GameTheoryEconomics.DigraphKInducible
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# five_inducible_tournament_threshold_le

Topic: social_choice   Node: a0fe9881c529

Provenance: helper lemma. Sanity lemma for five_inducible_tournament_threshold (OP-2174)

If some tournament on Fin m is not 5-inducible, then five_inducible_tournament_threshold ≤ m.
-/

theorem five_inducible_tournament_threshold_le (m : ℕ) (D : Digraph (Fin m))
    (hD : digraph_is_tournament D) (hnot : ¬ digraph_k_inducible 5 D) :
    five_inducible_tournament_threshold ≤ m := Nat.sInf_le ⟨D, hD, hnot⟩
