import AFTD.Prelude

/-!
# is_jointly_measurable_on

Topic: quantum   Node: c3a4658b0a4c

Provenance: formalization of a published result. Source: arXiv:2610.37347 Eq. (2) and Corollary 1

A family of k binary measurements M on C^d is jointly measurable on a subspace with orthogonal projection P if there exists a parent POVM G of positive semidefinite matrices indexed by Bool^k summing to P whose marginal for each measurement j equals the compressed effect P * M_j * P.
-/

/-- Joint measurability (compatibility) of k binary measurements on a subspace with orthogonal projection P. -/
def is_jointly_measurable_on {d k : ℕ}
    (M : Fin k → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ) : Prop := open scoped ComplexOrder in
  ∃ G : (Fin k → Bool) → Matrix (Fin d) (Fin d) ℂ,
    (∀ s, (G s).PosSemidef) ∧
    (∑ s, G s = P) ∧
    ∀ j : Fin k, (∑ s, if s j then G s else 0) = P * M j * P
