import AFTD.Prelude
import AFTD.Kb.Tcs.DfaSubsetResetThreshold
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing

/-!
# dfa_is_seq_subset_sync_choice

Topic: automata   Node: 5d958c048488

Provenance: formalization of a published result. Source: arXiv:2611.09136

Given an alphabet type α, a natural number k, a family of state types σ : Fin k → Type*, a family of deterministic finite automata A : (i : Fin k) → DFA α (σ i), and a sequence of words ws : Fin k → List α, ws is a sequential subset synchronization choice if for every index i : Fin k, ws i is a shortest word subset-synchronizing the set Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten)), with length in WithTop ℕ equal to the subset reset threshold of that set in A i.
-/

/-- A sequence of words forms a sequential subset synchronization choice if each word is a shortest word subset-synchronizing the current state image of the corresponding automaton. -/
def dfa_is_seq_subset_sync_choice {α : Type*} {k : ℕ} {σ : Fin k → Type*}
    (A : (i : Fin k) → DFA α (σ i)) (ws : Fin k → List α) : Prop := ∀ i : Fin k,
    let S_i := Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten))
    dfa_is_subset_synchronizing (A i) S_i (ws i) ∧
    ((ws i).length : WithTop ℕ) = dfa_subset_reset_threshold (A i) S_i
