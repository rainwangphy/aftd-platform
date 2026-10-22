import AFTD.Prelude

/-!
# efx_po_values

Topic: fair_division   Node: 5c819c784beb

Provenance: formalization of a published result. Source: arXiv:2610.29201 Theorem 1

The valuation matrix with 4 agents and 8 goods where agents 0 through 3 have values ![7, 6, 3, 3, 1, 1, 2, 1], ![6, 7, 1, 3, 3, 1, 1, 2], ![7, 6, 1, 1, 3, 3, 2, 1], and ![6, 7, 3, 1, 1, 3, 1, 2] respectively.
-/

/-- The integer valuation matrix for the 4-agent, 8-good instance showing incompatibility of EFX and Pareto optimality. -/
def efx_po_values : Fin 4 → Fin 8 → ℕ :=
  ![![7, 6, 3, 3, 1, 1, 2, 1],
    ![6, 7, 1, 3, 3, 1, 1, 2],
    ![7, 6, 1, 1, 3, 3, 2, 1],
    ![6, 7, 3, 1, 1, 3, 1, 2]]
