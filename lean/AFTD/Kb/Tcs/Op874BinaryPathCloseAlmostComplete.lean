import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BinaryChain
import AFTD.Kb.Tcs.Op874BinaryChainContainsPermutation

/-!
# op874_binary_path_close_almost_complete

Topic: graphs   Node: c8efce4dcf5c

Provenance: helper lemma. Finite local-phase reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

A finite chain of two-state constraints that each contains a bijection can be closed by any constraint excluding at most one pair.
-/

theorem op874_binary_path_close_almost_complete
    (rs : List (Bool → Bool → Prop)) (R : Bool → Bool → Prop)
    (hr : ∀ T ∈ rs, ∃ f : Bool → Bool, f false ≠ f true ∧ ∀ a, T a (f a))
    (hR : ∀ a b c d : Bool, (a,b) ≠ (c,d) → R a b ∨ R c d) :
    ∃ a b, op874_binary_chain rs a b ∧ R b a := by
  obtain ⟨f, -, hf⟩ := op874_binary_chain_contains_permutation rs hr
  have h := hR (f false) false (f true) true (by intro he; have := congrArg Prod.snd he; cases this)
  rcases h with h | h
  · exact ⟨false, f false, hf false, h⟩
  · exact ⟨true, f true, hf true, h⟩
