import AFTD.Prelude

/-!
# gaussKronFam

Topic: quantum   Node: 778c30b51ea9

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

The threefold tensor product of a family of 2x2 matrices, indexed by (Fin 3 → Fin 2), as an entrywise product.
-/

/-- Entrywise threefold tensor product of a family of 2×2 matrices over Fin 3 → Fin 2. -/
noncomputable def gaussKronFam (A : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := fun x y => ∏ q, A q (x q) (y q)
