import AFTD.Prelude
import AFTD.Kb.Tcs.NfaMaxAmbiguity
import AFTD.Kb.Tcs.NfaIsTrim
import AFTD.Kb.Tcs.NfaDegreeOfAmbiguity
import AFTD.Kb.Tcs.NfaIsFinitelyAmbiguous

/-!
# le_nfa_max_ambiguity

Topic: automata   Node: 6211b285dc4b

Provenance: helper lemma. arXiv:2610.08525 Sec. 5

For any natural numbers n and k and any trim finitely ambiguous NFA M with n states over alphabet Fin k, the degree of ambiguity of M is at most the maximum ambiguity M(n).
-/

/-- The degree of ambiguity of any trim finitely ambiguous NFA is bounded above by nfa_max_ambiguity. -/
theorem le_nfa_max_ambiguity (n k : ℕ) (M : NFA (Fin k) (Fin n))
    (ht : nfa_is_trim M) (hf : nfa_is_finitely_ambiguous M) :
    nfa_degree_of_ambiguity M ≤ nfa_max_ambiguity n := by
  unfold nfa_max_ambiguity
  exact le_iSup_of_le k (le_iSup_of_le M (le_iSup_of_le ht (le_iSup_of_le hf le_rfl)))
