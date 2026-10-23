import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_spectra

Topic: graphs   Node: 41b93a4186db

Provenance: formalization of a published result. Source: scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:161

The set Lambda_n of all complex eigenvalues of standardized Laplacian matrices of order n.
-/

/-- The set of all complex eigenvalues of standardized Laplacian matrices of order n. -/
def standardized_laplacian_spectra (n : ℕ) : Set ℂ := { z : ℂ | ∃ L : Matrix (Fin n) (Fin n) ℝ, is_standardized_laplacian n L ∧ z ∈ spectrum ℂ (L.map Complex.ofReal) }
