import AFTD.Prelude
import AFTD.Kb.Tcs.MaskURuns
import AFTD.Kb.Tcs.IsWordMask

/-!
# word_insertion_degree

Topic: automata   Node: b4c4163888c9

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 3

The minimum insertion degree word_insertion_degree u v w of word w with respect to source words u and v is the infimum in WithTop Nat of mask_u_runs M over all binary masks M satisfying is_word_mask u v w M.
-/

/-- Minimum insertion degree of w with respect to sources u, v, or top if w is not a shuffle. -/
noncomputable def word_insertion_degree {α : Type*} (u v w : List α) : WithTop ℕ :=
  sInf { (mask_u_runs M : WithTop ℕ) | (M : List Bool) (_ : is_word_mask u v w M) }
