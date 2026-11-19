import AFTD.Prelude

/-!
# four_values_covering_fin_four_are_distinct

Topic: combinatorics   Node: 41edf61a08df

Provenance: helper lemma. Seven-cycle palette counting kernel for the OP-874 campaign.

Four values that cover a four-element palette are pairwise distinct.
-/

theorem four_values_covering_fin_four_are_distinct
    (a b c d : Fin 4) (h : ∀ k : Fin 4, k = a ∨ k = b ∨ k = c ∨ k = d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  let f : Fin 4 → Fin 4 := ![a,b,c,d]
  have hs : Function.Surjective f := by
    intro k
    rcases h k with ha | hb | hc | hd
    · exact ⟨0, by simpa [f] using ha.symm⟩
    · exact ⟨1, by simpa [f] using hb.symm⟩
    · exact ⟨2, by simpa [f] using hc.symm⟩
    · exact ⟨3, by simpa [f] using hd.symm⟩
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact (by decide : (0 : Fin 4) ≠ 1) (hi (by simpa [f] using heq))
  · intro heq
    exact (by decide : (0 : Fin 4) ≠ 2) (hi (by simpa [f] using heq))
  · intro heq
    exact (by decide : (0 : Fin 4) ≠ 3) (hi (by simpa [f] using heq))
  · intro heq
    exact (by decide : (1 : Fin 4) ≠ 2) (hi (by simpa [f] using heq))
  · intro heq
    exact (by decide : (1 : Fin 4) ≠ 3) (hi (by simpa [f] using heq))
  · intro heq
    exact (by decide : (2 : Fin 4) ≠ 3) (hi (by simpa [f] using heq))
