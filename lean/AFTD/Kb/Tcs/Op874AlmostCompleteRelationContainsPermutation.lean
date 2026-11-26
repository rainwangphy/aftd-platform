import AFTD.Prelude

/-!
# op874_almost_complete_relation_contains_permutation

Topic: graphs   Node: 9f35fa2e08da

Provenance: helper lemma. Finite local-phase reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

A two-state relation that excludes at most one ordered pair contains a bijection.
-/

theorem op874_almost_complete_relation_contains_permutation
    (R : Bool → Bool → Prop)
    (hR : ∀ a b c d : Bool, (a,b) ≠ (c,d) → R a b ∨ R c d) :
    ∃ f : Bool → Bool, f false ≠ f true ∧ ∀ a, R a (f a) := by
  classical
  by_cases h00 : R false false
  · by_cases h11 : R true true
    · exact ⟨id, by decide, by intro a; cases a <;> simp_all⟩
    · have h01 := hR false true true true (by decide)
      have h10 := hR true false true true (by decide)
      refine ⟨Bool.not, by decide, ?_⟩
      intro a; cases a <;> simp_all
  · have h01 := hR false true false false (by decide)
    have h10 := hR true false false false (by decide)
    refine ⟨Bool.not, by decide, ?_⟩
    intro a; cases a <;> simp_all
