import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentExistsDecyclingFamily
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphInvert

/-!
# tournament_exists_family_length_eq_inversion_number

Topic: graphs   Node: fb0ed128a298

Provenance: helper lemma. Helper for the bounds on inversion numbers of dijoins in arXiv:2610.13798 (Sec. 1 and Sec. 4): the infimum defining inv(D) is a minimum.

For a finite tournament D, the inversion number is attained: some decycling family of D has exactly inv(D) sets.
-/

theorem tournament_exists_family_length_eq_inversion_number (V : Type) [Fintype V]
    (D : Digraph V) (h : digraph_is_tournament D) :
    ∃ Xs : List (Set V), Xs.length = digraph_inversion_number D ∧
      digraph_is_acyclic (Xs.foldl digraph_invert D) := by
  obtain ⟨Xs, hXs⟩ := tournament_exists_decycling_family V D h
  have hne : Set.Nonempty {p | ∃ Xs : List (Set V), Xs.length = p ∧
      digraph_is_acyclic (Xs.foldl digraph_invert D)} := ⟨Xs.length, Xs, rfl, hXs⟩
  exact Nat.sInf_mem hne
