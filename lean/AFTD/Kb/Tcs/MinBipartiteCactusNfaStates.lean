import AFTD.Prelude
import AFTD.Kb.Tcs.IsBipartiteCactusNfa

/-!
# min_bipartite_cactus_nfa_states

Topic: automata   Node: 921ba6970cf6

Provenance: formalization of a published result. Source: arXiv:2610.11717 Sec. 4

The minimum number of states in an epsilon-free NFA accepting L whose transition graph is a bipartite cactus.
-/

/-- Minimum number of states in an epsilon-free NFA accepting L whose transition graph is a bipartite cactus. -/
noncomputable def min_bipartite_cactus_nfa_states {α : Type*} (L : Language α) : ℕ := sInf { k : ℕ | ∃ (σ : Type) (_ : Fintype σ) (A : NFA α σ),
    Fintype.card σ = k ∧ A.accepts = L ∧ is_bipartite_cactus_nfa A }
