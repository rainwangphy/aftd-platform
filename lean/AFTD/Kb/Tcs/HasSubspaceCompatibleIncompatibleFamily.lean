import AFTD.Prelude

/-!
# has_subspace_compatible_incompatible_family

Topic: quantum   Node: b71ad85e7991

Provenance: formalization of a published result. Source: arXiv:2610.37347 Corollary 1

There exists a family of k binary measurements on C^d that is incompatible on C^d but whose compression to every proper subspace is jointly measurable.
-/

/-- Existence of a family of k binary measurements on C^d that is incompatible globally on C^d but jointly measurable after compression to every proper subspace. -/
def has_subspace_compatible_incompatible_family (d k : ℕ) : Prop := open scoped ComplexOrder in
  ∃ M : Fin k → Matrix (Fin d) (Fin d) ℂ,
    (∀ j, (M j).PosSemidef ∧ (1 - M j).PosSemidef) ∧
    (¬ ∃ G : (Fin k → Bool) → Matrix (Fin d) (Fin d) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = 1) ∧
      ∀ j : Fin k, (∑ s, if s j then G s else 0) = M j) ∧
    ∀ P : Matrix (Fin d) (Fin d) ℂ, P.IsHermitian ∧ P * P = P ∧ P.rank < d →
      ∃ G : (Fin k → Bool) → Matrix (Fin d) (Fin d) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = P) ∧
        ∀ j : Fin k, (∑ s, if s j then G s else 0) = P * M j * P
