import AFTD.Prelude

/-!
# is_config_in_all_products

Topic: combinatorics   Node: bba3aa47939b

Provenance: formalization of a published result. Source: arXiv:2610.13987, Definition 2

A binary matrix F is a configuration in every p-fold product of matrices from {I_m, I_m^c, T_m} for all sufficiently large m.
-/

/-- Predicate that a binary matrix F is a configuration in every p-fold product of identity, complement of identity, or triangular matrices of size m for all sufficiently large m. -/
def is_config_in_all_products {m_F n_F : Type*}
    (F : Matrix m_F n_F Bool) (p : ℕ) : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∀ τ : Fin p → Fin 3,
      ∃ (r : m_F → Fin p × Fin m) (c : n_F → Fin p → Fin m),
        Function.Injective r ∧ Function.Injective c ∧
        ∀ i j,
          (match τ (r i).1 with
          | 0 => (r i).2 == (c j) (r i).1
          | 1 => (r i).2 ≠ (c j) (r i).1
          | _ => ((r i).2 : ℕ) ≤ (((c j) (r i).1) : ℕ)) = F i j
