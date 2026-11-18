import AFTD.Prelude

/-!
# grid_rho

Topic: combinatorics   Node: 74b33b0aa069

Provenance: formalization of a published result. Source: arXiv:2611.19635, Section 3, Definition 3.1

The minimum number of monochromatic rectangles in any 2-coloring of the 2D grid [a] × [b], where a rectangle is given by a pair of 2-element subsets of rows and columns.
-/

/-- The parameter ρ(a, b): the minimum number of monochromatic rectangles in any 2-coloring of an a × b grid. -/
noncomputable def grid_rho (a b : ℕ) : ℕ := ((Finset.univ : Finset (Fin a → Fin b → Bool)).image
  (fun g => (((Finset.powersetCard 2 (Finset.univ : Finset (Fin a))) ×ˢ
    (Finset.powersetCard 2 (Finset.univ : Finset (Fin b)))).filter
      (fun (s, t) => ∃ col : Bool, ∀ x ∈ s, ∀ y ∈ t, g x y = col)).card)).min'
    (Finset.Nonempty.image Finset.univ_nonempty _)
