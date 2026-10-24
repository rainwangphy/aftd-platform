import AFTD.Prelude

/-!
# octagon_section_plane_facets_val

Topic: integer_programming   Node: 8d37b34e5ff8

Provenance: helper lemma. step towards polygon_psd_rank_four_attains_eight

The underlying function of the eight facet functionals of P_2: X ↦ 1 - (a_i X_0 + b_i X_1) with facet normals a=(1/2,1/2,-1/2,-1/2,3/2,3/2,-3/2,-3/2), b=(3/2,-3/2,3/2,-3/2,1/2,-1/2,1/2,-1/2).
-/

/-- The facet functionals of P_2 as plain functions (the assembly lemma lifts these to affine maps). -/
noncomputable def octagon_section_plane_facets_val : Fin 8 → (Fin 2 → ℝ) → ℝ := fun i X => 1 - ((![1/2,1/2,-1/2,-1/2,3/2,3/2,-3/2,-3/2] : Fin 8 → ℝ) i * X 0
                + (![3/2,-3/2,3/2,-3/2,1/2,-1/2,1/2,-1/2] : Fin 8 → ℝ) i * X 1)
