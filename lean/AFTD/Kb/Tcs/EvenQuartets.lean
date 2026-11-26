import AFTD.Prelude

/-!
# even_quartets

Topic: combinatorics   Node: a0c79cca98f5

Provenance: formalization of a published result. Source: scout/2611-32833-even-quartets-and-the-maximum-density-of-a-simplical-3-cocy.md:108

Given a 2-coloring of triples represented by χ : Finset (Fin n) → ZMod 2, the even quartets are the 4-element subsets Q of Fin n such that the sum of χ over all triples in Q is 0.
-/

/-- The set of even quartets (4-subsets with an even number of red triples) for a triple coloring χ. -/
def even_quartets (n : ℕ) (χ : Finset (Fin n) → ZMod 2) : Finset (Finset (Fin n)) := ((Finset.univ : Finset (Fin n)).powersetCard 4).filter
    (fun Q => ∑ T ∈ Q.powersetCard 3, χ T = 0)
