import AFTD.Prelude
import AFTD.Kb.Tcs.EvenQuartets

/-!
# min_even_quartets_count

Topic: combinatorics   Node: 5a0f5f73ac5a

Provenance: formalization of a published result. Source: scout/2611-32833-even-quartets-and-the-maximum-density-of-a-simplical-3-cocy.md:110

The minimum number TC(n) of even quartets over all 2-colorings of triples on n vertices, where an even quartet has an even number of red triples (sum 0 in ZMod 2).
-/

/-- The minimum number TC(n) of even quartets over all 2-colorings of triples on n vertices. -/
def min_even_quartets_count (n : ℕ) : ℕ := ((((Finset.univ : Finset (Fin n)).powersetCard 3).powerset).image
    (fun H (s : Finset (Fin n)) => if s ∈ H then (1 : ZMod 2) else (0 : ZMod 2))).inf'
    ⟨(fun (s : Finset (Fin n)) => if s ∈ (∅ : Finset (Finset (Fin n))) then (1 : ZMod 2) else (0 : ZMod 2)),
      Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr (Finset.empty_subset _))⟩
    (fun χ => (even_quartets n χ).card)
