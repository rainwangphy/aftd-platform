import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimFinLookup

/-!
# pyranim_seq_first_empty

Topic: combinatorial_games   Node: 6c4339463ffa

Provenance: helper lemma. step towards pyranim_card_stable_positions

pyranim_seq_first_empty n l is the least j with 0 < j < n+1 and l(j) = j+2, that is the first column after the first one that is empty; it is 0 if no such index exists.
-/

/-- The least index at which the sequence has an empty column (value j+2), or 0 if there is none. -/
noncomputable def pyranim_seq_first_empty (n : ℕ) (l : Fin (n + 1) → Fin (n + 3)) : ℕ := by
  classical
  exact if h : ∃ j, 0 < j ∧ j < n + 1 ∧ pyranim_fin_lookup (n + 1) l j = j + 2 then Nat.find h else 0
