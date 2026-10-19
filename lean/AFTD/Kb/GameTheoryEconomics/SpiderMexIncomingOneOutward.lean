import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt
import AFTD.Kb.GameTheoryEconomics.SpiderRhoZeroSame
import AFTD.Kb.GameTheoryEconomics.SpiderRhoPairValues
import AFTD.Kb.GameTheoryEconomics.SpiderMexIncomingOneOutwardNotMem
import AFTD.Kb.GameTheoryEconomics.SpiderMexIncomingOneOutwardAllLtMem
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_mex_incoming_one_outward

Topic: combinatorial_games   Node: 2e056eb94ff2

Provenance: helper lemma. step towards spider_blocked_incoming_one_outward

The minimum excluded value of the explicit options list for the configuration κ₂ = (in;{(1,outward),(r,φ)}) equals r ^^^ 1 for every r ≥ 2 and φ ≠ free.
-/

lemma spider_mex_incoming_one_outward_of_not_mem_and_all_lt_mem (l : List ℕ) (m : ℕ)
    (h_not_mem : m ∉ l) (h_all_lt : ∀ k < m, k ∈ l) : nat_mex_list l = m := by
  have ⟨h1, h2⟩ := nat_mex_list_not_mem_and_lt l
  rcases lt_trichotomy (nat_mex_list l) m with hlt | heq | hgt
  · exact (h1 (h_all_lt (nat_mex_list l) hlt)).elim
  · exact heq
  · exact (h_not_mem (h2 m hgt)).elim

/-- The mex of the explicit closed-form option list of the configuration κ₂ = (in;{(1,outward),(r,φ)}) equals r ^^^ 1 for every r ≥ 2 and φ ≠ free. -/
theorem spider_mex_incoming_one_outward (r : ℕ) (hr : 2 ≤ r) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    nat_mex_list
      ([r, spider_rho (r - 1) SpiderLegEnd.inward φ ^^^ 1, spider_rho (r - 1) SpiderLegEnd.outward φ ^^^ 1] ++
       (List.range (r - 2)).flatMap (fun idx =>
         let i := idx + 1
         [spider_rho (r - 1 - i) SpiderLegEnd.inward φ ^^^ (i ^^^ 1),
          spider_rho (r - 1 - i) SpiderLegEnd.outward φ ^^^ (i ^^^ 1)]) ++
       [spider_rho 0 φ φ ^^^ ((r - 1) ^^^ 1)]) = r ^^^ 1 := by
  apply spider_mex_incoming_one_outward_of_not_mem_and_all_lt_mem
  · exact spider_mex_incoming_one_outward_not_mem r hr φ hφ
  · exact spider_mex_incoming_one_outward_all_lt_mem r hr φ hφ
