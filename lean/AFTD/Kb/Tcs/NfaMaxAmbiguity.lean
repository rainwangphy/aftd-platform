import AFTD.Prelude
import AFTD.Kb.Tcs.NfaIsTrim
import AFTD.Kb.Tcs.NfaIsFinitelyAmbiguous
import AFTD.Kb.Tcs.NfaDegreeOfAmbiguity

/-!
# nfa_max_ambiguity

Topic: automata   Node: bef702451441

Provenance: formalization of a published result. Source: arXiv:2610.08525 Sec. 5

The maximum degree of ambiguity M(n) in ℕ∞ over all trim finitely ambiguous nondeterministic finite automata with n states across all finite alphabets.
-/

/-- Maximum degree of ambiguity M(n) over all trim finitely ambiguous NFAs with n states. -/
noncomputable def nfa_max_ambiguity (n : ℕ) : ℕ∞ :=
  ⨆ (k : ℕ) (M : NFA (Fin k) (Fin n)) (_ : nfa_is_trim M) (_ : nfa_is_finitely_ambiguous M),
    nfa_degree_of_ambiguity M
