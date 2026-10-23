import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaMixedCount

/-!
# two_way_dfa_mixed_count_le

Topic: automata   Node: 0bf2ddf3cec3

Provenance: helper lemma. helper for arXiv:2610.18897 Corollary 7.2 (the bound 4n)

The number of mixed states is at most the number of states.
-/

theorem two_way_dfa_mixed_count_le {σ Q : Type*} [Finite Q] (A : two_way_dfa σ Q) :
    two_way_dfa_mixed_count A ≤ Nat.card Q :=
  Set.ncard_le_card _
