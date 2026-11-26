import AFTD.Prelude
import AFTD.Kb.Tcs.EvenQuartets

/-!
# min_even_quartet_density

Topic: combinatorics   Node: 9b928c81d0ca

Provenance: formalization of a published result. Source: scout/2611-32833-even-quartets-and-the-maximum-density-of-a-simplical-3-cocy.md:110

The minimum density m_n of even quartets among all 2-colorings of triples on n vertices, defined as TC(n) / binom(n, 4) for n ≥ 4 and 0 for n < 4, where an even quartet has sum 0 in ZMod 2.
-/

/-- The minimum density m_n of even quartets among all 2-colorings of triples on n vertices. -/
noncomputable def min_even_quartet_density (n : ℕ) : ℝ := if n < 4 then 0 else
  (((((Finset.univ : Finset (Fin n)).powersetCard 3).powerset).image
    (fun H (s : Finset (Fin n)) => if s ∈ H then (1 : ZMod 2) else (0 : ZMod 2))).inf'
    ⟨(fun (s : Finset (Fin n)) => if s ∈ (∅ : Finset (Finset (Fin n))) then (1 : ZMod 2) else (0 : ZMod 2)),
      Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr (Finset.empty_subset _))⟩
    (fun χ => ((even_quartets n χ).card : ℝ))) / (n.choose 4 : ℝ)
