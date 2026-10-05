import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCube
import AFTD.Kb.GameTheoryEconomics.GpaIndep
import AFTD.Kb.GameTheoryEconomics.GpaUStarLeIndep

/-!
# gpa_rhs_upper

Topic: mechanism_design   Node: 838eb30c0de4

Upper bound on the cube: u*(x) ≤ α(G) for every x ∈ [0,1]^k.
-/

open Finset in
/-- Upper bound on the cube: `u*(x) ≤ α(G)` for every `x ∈ [0,1]^k`. -/
lemma gpa_rhs_upper {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (a : ℕ) (hα : ∀ S, gpa_indep G S → S.card ≤ a)
    (x : Fin k → ℝ) (hx : x ∈ gpa_cube k) :
    gpa_uStar (gpa_adjMat G) x ≤ a := by
  obtain ⟨P, hP, hle⟩ := gpa_uStar_le_indep G x (fun i => (hx i).1)
  have h1 : ∑ i ∈ P, x i ≤ ∑ _i ∈ P, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hx i).2)
  have h2 : (P.card : ℝ) ≤ a := by exact_mod_cast hα P hP
  simp at h1
  linarith
