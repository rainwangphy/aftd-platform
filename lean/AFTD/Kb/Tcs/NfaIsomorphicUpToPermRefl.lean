import AFTD.Prelude
import AFTD.Kb.Tcs.NfaIsomorphicUpToPerm

/-!
# nfa_isomorphic_up_to_perm_refl

Topic: automata   Node: af75a92843fe

Provenance: helper lemma. folklore

Every NFA is isomorphic to itself up to state bijection and alphabet permutation, witnessed by the identity bijection on states and the identity permutation on the alphabet.
-/

/-- NFA isomorphism up to state bijection and alphabet permutation is reflexive. -/
theorem nfa_isomorphic_up_to_perm_refl {α σ : Type*} (M : NFA α σ) :
    nfa_isomorphic_up_to_perm M M := by
  unfold nfa_isomorphic_up_to_perm
  refine ⟨Equiv.refl σ, Equiv.refl α, ?_⟩
  simp
