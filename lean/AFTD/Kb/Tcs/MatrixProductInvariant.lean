import AFTD.Prelude
import AFTD.Kb.Tcs.IsConfigInAllProducts

/-!
# matrix_product_invariant

Topic: combinatorics   Node: 14ed6e64ea10

Provenance: formalization of a published result. Source: arXiv:2610.13987, Definition 2

The product invariant X(F) is the smallest positive integer p such that F embeds as a configuration in every p-fold product with factors chosen from {I_m, I_m^c, T_m} for all sufficiently large m.
-/

/-- The forbidden configuration product invariant X(F): the smallest positive integer p such that F is a configuration in every p-fold product of matrices from {I_m, I_m^c, T_m} for all sufficiently large m. -/
noncomputable def matrix_product_invariant {m_F n_F : Type*}
    (F : Matrix m_F n_F Bool) : ℕ :=
  sInf { p : ℕ | 1 ≤ p ∧ is_config_in_all_products F p }
