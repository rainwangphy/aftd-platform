import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.PairEncodeInjective

/-!
# dfa_is_synchronizing_subsingleton

Topic: automata   Node: f83436e04055

Provenance: helper lemma. folklore

Every word is synchronizing for a deterministic finite automaton whose state type is a subsingleton.
-/

/-- Every word synchronizes a DFA whose state type is a subsingleton. -/
theorem dfa_is_synchronizing_subsingleton {α σ : Type*} [Subsingleton σ] (A : DFA α σ) (w : List α) : dfa_is_synchronizing A w := by first | exact pair_encode_injective | (apply pair_encode_injective <;> assumption) | (apply pair_encode_injective <;> simp_all) | simpa using pair_encode_injective | (simp only [dfa_is_synchronizing] at *; first | exact pair_encode_injective | (apply pair_encode_injective <;> assumption) | (apply pair_encode_injective <;> simp_all) | simpa using pair_encode_injective)
