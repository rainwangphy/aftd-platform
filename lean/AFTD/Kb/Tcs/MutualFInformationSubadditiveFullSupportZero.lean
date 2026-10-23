import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformationSubadditiveFullSupport
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_subadditive_full_support_zero

Topic: information   Node: 9ed234211461

Provenance: helper lemma. sanity lemma for mutual_f_information_subadditive_full_support

Sanity: the zero generator f = 0 is subadditive on full-support distributions (every mutual f-information is 0).
-/

theorem mutual_f_information_subadditive_full_support_zero :
    mutual_f_information_subadditive_full_support (fun _ => 0) := by
  intro X Y Z _ _ _ pX PY PZ _ _ _ _ _ _
  simp [mutual_f_information]
