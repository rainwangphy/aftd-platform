import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing

/-!
# dfa_subset_reset_threshold

Topic: automata   Node: 6480ae20a0e6

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7

The subset reset threshold `dfa_subset_reset_threshold A S` of a subset `S` of states of a DFA `A` is the infimum in `WithTop ℕ` of the lengths of all words that subset-synchronize `S`.
-/

/-- The subset reset threshold of a subset S in a DFA is the infimum of lengths of words that subset-synchronize S. -/
noncomputable def dfa_subset_reset_threshold {α σ : Type*} (A : DFA α σ) (S : Set σ) : WithTop ℕ := sInf ((fun w : List α => (w.length : WithTop ℕ)) '' { w | dfa_is_subset_synchronizing A S w })
