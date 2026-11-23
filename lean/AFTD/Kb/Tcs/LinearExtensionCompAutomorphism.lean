import AFTD.Prelude
import AFTD.Kb.Tcs.IsPosetLinearExtension

/-!
# linear_extension_comp_automorphism

Topic: combinatorics   Node: f78ca58a26f8

Provenance: formalization of a published result. Source: arXiv:2611.26888 Proposition 3.1

If l is a linear extension of a finite poset P and f is a poset automorphism of P, then l ∘ f is a linear extension of P.
-/

/-- Composition of a linear extension with a poset automorphism is a linear extension. -/
theorem linear_extension_comp_automorphism {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (hl : is_poset_linear_extension l) (f : P ≃o P) :
    is_poset_linear_extension (l ∘ f) := ⟨hl.1.comp f.bijective, fun _ _ hxy => hl.2 (f.monotone hxy)⟩
