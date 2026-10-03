import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LxvValues
import AFTD.Kb.GameTheoryEconomics.LxvVal
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# lxv_sum_bundle

Topic: fair_division   Node: 7eb270efaff2

The integer value of a bundle equals the explicit six-term sum lxv_val.
-/

lemma lxv_sum_bundle (a : Fin 6 → Fin 4) (i j : Fin 4) :
    ∑ g ∈ bundle_of a j, lxv_values i g = lxv_val a i j := by
  simp [bundle_of, Finset.sum_filter, Fin.sum_univ_six, lxv_val]
