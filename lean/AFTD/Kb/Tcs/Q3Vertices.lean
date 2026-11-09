import AFTD.Prelude

/-!
# q3_vertices

Topic: combinatorics   Node: 9e1b1ade1969

Provenance: formalization of a published result. Source: arXiv:2611.08819 Section 2

The finite set of 21 vectors in Fin 3 → ℤ containing precisely ![6, -6, 0], ![4, 0, -2], ![3, 1, -2], ![3, 0, 0], ![3, 0, -3], ![2, 1, -1], ![2, -2, 2], ![1, 1, -1], ![1, 0, 1], ![1, -1, 2], ![0, 0, -3], ![0, -1, 2], ![0, -3, 3], ![0, -6, 0], ![0, -6, -6], ![-1, 0, 0], ![-1, 0, -1], ![-1, -2, 2], ![-2, -1, -1], ![-2, -2, -2], and ![-3, -3, 0].
-/

/-- The 21 lattice points in ℤ^3 generating the 3-dimensional polytope Q_3. -/
def q3_vertices : Finset (Fin 3 → ℤ) := { ![6, -6, 0],
    ![4, 0, -2],
    ![3, 1, -2],
    ![3, 0, 0],
    ![3, 0, -3],
    ![2, 1, -1],
    ![2, -2, 2],
    ![1, 1, -1],
    ![1, 0, 1],
    ![1, -1, 2],
    ![0, 0, -3],
    ![0, -1, 2],
    ![0, -3, 3],
    ![0, -6, 0],
    ![0, -6, -6],
    ![-1, 0, 0],
    ![-1, 0, -1],
    ![-1, -2, 2],
    ![-2, -1, -1],
    ![-2, -2, -2],
    ![-3, -3, 0] }
