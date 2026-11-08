import AFTD.Prelude

/-!
# rat_row_kernel

Topic: elementary_number_theory   Node: 9d0ac96572e1

Provenance: helper lemma. step towards view_obstruction_unresolved_node_infinite_witnesses

For integer rows w_1,...,w_k ∈ ℤ^n, the ℚ-subspace of ℚ^n consisting of rational vectors orthogonal to all rows, i.e. the kernel of the linear map y ↦ (⟨w_i, y⟩)_i.
-/

/-- The rational row-kernel of a finite family of integer rows. -/
noncomputable def rat_row_kernel {k n : ℕ} (w : Fin k → Fin n → ℤ) : Submodule ℚ (Fin n → ℚ) := LinearMap.ker (LinearMap.pi (fun i : Fin k =>
      ∑ j : Fin n, (w i j : ℚ) • (LinearMap.proj j)))
