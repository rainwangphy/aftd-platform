import AFTD.Prelude
import AFTD.Kb.Tcs.DfaSubsetResetThreshold
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing

/-!
# dfa_stage_has_unique_shortest_choice

Topic: automata   Node: c2242b8b94b3

Provenance: formalization of a published result. Source: arXiv:2611.09136

Given an alphabet type α, a natural number k, a family of state types σ : Fin k → Type*, a family of deterministic finite automata A : (i : Fin k) → DFA α (σ i), a sequence of choices ws : Fin k → List α, and an index i : Fin k, stage i has a unique shortest choice if there exists a unique word w : List α such that w subset-synchronizes the set Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten)) and the length of w in WithTop ℕ equals the subset reset threshold of that set in A i.
-/

/-- A stage of sequential subset synchronization has a unique shortest choice if there is a unique shortest subset-synchronizing word for the current state image. -/
def dfa_stage_has_unique_shortest_choice {α : Type*} {k : ℕ} {σ : Fin k → Type*}
    (A : (i : Fin k) → DFA α (σ i)) (ws : Fin k → List α) (i : Fin k) : Prop := ∃! w : List α,
    let S_i := Set.range (fun q : σ i => (A i).evalFrom q (((List.ofFn ws).take i.val).flatten))
    dfa_is_subset_synchronizing (A i) S_i w ∧
    (w.length : WithTop ℕ) = dfa_subset_reset_threshold (A i) S_i
