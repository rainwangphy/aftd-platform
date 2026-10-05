import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaPath3

/-!
# gpa_path3_indep

Topic: mechanism_design   Node: 5ff18d23316b

In the path 0 - 2 - 1, {0, 1} is a maximum independent set.
-/

open Finset in
/-- In the path `0 - 2 - 1`, `{0, 1}` is a maximum independent set. -/
lemma gpa_path3_indep : gpa_indep gpa_path3 {0, 1} ∧
    ∀ S, gpa_indep gpa_path3 S → S.card ≤ ({0, 1} : Finset (Fin 3)).card := by
  refine ⟨by unfold gpa_indep gpa_path3; decide, ?_⟩
  intro S hS
  have : S ≠ Finset.univ := by
    rintro rfl
    exact hS 0 (Finset.mem_univ _) 2 (Finset.mem_univ _) (by unfold gpa_path3; decide)
  have hlt : S.card < 3 := by
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 this)
    simpa using this
  have : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  omega
