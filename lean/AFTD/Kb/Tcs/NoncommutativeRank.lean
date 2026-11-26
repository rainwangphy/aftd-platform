import AFTD.Prelude

/-!
# noncommutative_rank

Topic: algebraic_complexity   Node: 8456857a6c02

Provenance: formalization of a published result. Source: arXiv:2611.31963 Section 2.1; Fortin-Reutenauer (2004) Theorem 1

For an explicit field F, implicit dimensions a and b, an arbitrary indexing type ι, and a family of rectangular matrices A : ι → Matrix (Fin a) (Fin b) F, noncommutative_rank F A is the infimum sInf of the set of natural numbers k for which there exist an F-subspace U of Fin b → F and an F-subspace V of Fin a → F such that for all i : ι, Submodule.map (A i).mulVecLin U ≤ V, and k = (b - Module.finrank F U) + Module.finrank F V.
-/

/-- The noncommutative rank of a linear symbolic matrix via Fortin-Reutenauer duality. -/
noncomputable def noncommutative_rank (F : Type*) [Field F] {a b : ℕ} {ι : Type*}
    (A : ι → Matrix (Fin a) (Fin b) F) : ℕ := sInf { k : ℕ | ∃ (U : Subspace F (Fin b → F)) (V : Subspace F (Fin a → F)),
    (∀ i, Submodule.map (A i).mulVecLin U ≤ V) ∧
    k = (b - Module.finrank F U) + Module.finrank F V }
