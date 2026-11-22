import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinner

/-!
# four_voters_simple_rule

Topic: social_choice   Node: e696c965c2dd

Provenance: helper lemma. step towards op_2119_four_voters_four_alternatives_nomg_exists

The voting rule on Fin 4 with 4 voters that selects the Condorcet winner if one exists, and candidate 0 otherwise.
-/

/-- The simple voting rule on Fin 4 with 4 voters choosing the Condorcet winner if one exists, and 0 otherwise. -/
noncomputable def four_voters_simple_rule (P : Fin 4 → LinearOrder (Fin 4)) : Fin 4 := open Classical in
  if h : ∃ x, is_condorcet_winner P x then Classical.choose h else 0
