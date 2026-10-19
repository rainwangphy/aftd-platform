import AFTD.Prelude
import AFTD.Kb.Tcs.NfaIsTrim
import AFTD.Kb.Tcs.NfaIsFinitelyAmbiguous
import AFTD.Kb.Tcs.NfaDegreeOfAmbiguity

/-!
# finitely_ambiguous_nfa_single_state_unambiguous

Topic: automata   Node: d3c5f2562ecf

Provenance: formalization of a published result. Source: arXiv:2610.08525 Claim 2

For every natural number k and every trim finitely ambiguous NFA M with alphabet Fin k and 1 state, the degree of ambiguity of M in ℕ∞ is at most 1.
-/

/-- Every trim finitely ambiguous NFA with 1 state has degree of ambiguity at most 1. -/
theorem finitely_ambiguous_nfa_single_state_unambiguous
    (k : ℕ) (M : NFA (Fin k) (Fin 1)) (ht : nfa_is_trim M) (hf : nfa_is_finitely_ambiguous M) :
    nfa_degree_of_ambiguity M ≤ 1 := by
  have _ := ht
  have _ := hf
  unfold nfa_degree_of_ambiguity
  apply iSup_le
  intro w
  rw [Set.encard_le_one_iff_subsingleton]
  intro x _ y _
  exact Subsingleton.elim x y
