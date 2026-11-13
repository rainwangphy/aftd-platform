import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimFinLookup
import AFTD.Kb.GameTheoryEconomics.PyranimFullPyramid

/-!
# pyranim_seq_ideal

Topic: combinatorial_games   Node: 240ef5d5481e

Provenance: helper lemma. step towards pyranim_card_stable_positions

For a sequence l : Fin n → Fin (n+2), pyranim_seq_ideal n l is the set of chips (a,b) of the n-tier pyramid with l(b-1) ≤ a: each column b is the interval {l(b-1), ..., b}.
-/

/-- The Pyranim position attached to a column-minimum sequence l: (a,b) is present iff l (b-1) ≤ a. -/
noncomputable def pyranim_seq_ideal (n : ℕ) (l : Fin n → Fin (n + 2)) : Finset (ℕ × ℕ) := (pyranim_full_pyramid n).filter fun p => pyranim_fin_lookup n l (p.2 - 1) ≤ p.1
