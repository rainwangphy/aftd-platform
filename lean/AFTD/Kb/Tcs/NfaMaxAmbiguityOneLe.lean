import AFTD.Prelude
import AFTD.Kb.Tcs.NfaMaxAmbiguity
import AFTD.Kb.Tcs.FinitelyAmbiguousNfaSingleStateUnambiguous
import AFTD.Kb.Tcs.NfaIsFinitelyAmbiguous
import AFTD.Kb.Tcs.NfaIsTrim
import AFTD.Kb.Tcs.NfaDegreeOfAmbiguity

/-!
# nfa_max_ambiguity_one_le

Topic: automata   Node: 10f7cf9c7f6e

Provenance: helper lemma. arXiv:2610.08525 Sec. 2

The maximum degree of ambiguity M(1) of trim finitely ambiguous nondeterministic finite automata with 1 state is at most 1.
-/

/-- The maximum degree of ambiguity of 1-state trim finitely ambiguous NFAs is at most 1. -/
theorem nfa_max_ambiguity_one_le : nfa_max_ambiguity 1 ≤ 1 := by
  unfold nfa_max_ambiguity
  apply iSup_le
  intro k
  apply iSup_le
  intro M
  apply iSup_le
  intro ht
  apply iSup_le
  intro hf
  exact finitely_ambiguous_nfa_single_state_unambiguous k M ht hf
