import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DigraphKInducible
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# five_inducible_tournament_threshold

Topic: social_choice   Node: d60fbdb3d6eb

Provenance: formalization of a published result. Source: arXiv:2611.27965 (Recognizing k-inducible Digraphs is NP-complete), Section 1: the minimum number of alternatives of a tournament that is not 5-inducible, the quantity OP-2174 asks to determine

The least natural number n such that some tournament D on the vertex set Fin n (digraph_is_tournament D: loopless, and for distinct x, y exactly one of x → y, y → x) is not 5-inducible (digraph_k_inducible 5 D fails); defined as the infimum (sInf) of the set of such n in ℕ.
-/

noncomputable def five_inducible_tournament_threshold : ℕ :=
  sInf {n : ℕ | ∃ D : Digraph (Fin n), digraph_is_tournament D ∧ ¬ digraph_k_inducible 5 D}
