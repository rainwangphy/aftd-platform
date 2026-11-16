import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op1370_three_point_paired_singleton_equality

Topic: combinatorics   Node: 2e542e011d14

Provenance: helper lemma. A finite two-family equality configuration for OP-1370, experiment 28768.

There are two nonempty uncomplemented strongly incomparable families on three coordinates, one a singleton with its complement in the other family, whose total size is four.
-/

theorem op1370_three_point_paired_singleton_equality :
    ∃ 𝒜 : Fin 2 → Finset (Finset (Fin 3)),
      (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧
      strongly_incomparable 𝒜 ∧ (𝒜 0).card = 1 ∧
      (∃ S ∈ 𝒜 0, Sᶜ ∈ 𝒜 1) ∧ (∑ i, (𝒜 i).card) = 2 ^ (3-1) := by
  open Finset in
  let F : Fin 2 → Finset (Finset (Fin 3)) := ![{{0,1}}, {{2}, {0,2}, {1,2}}]
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · unfold is_uncomplemented
    decide +kernel
  · unfold strongly_incomparable
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
