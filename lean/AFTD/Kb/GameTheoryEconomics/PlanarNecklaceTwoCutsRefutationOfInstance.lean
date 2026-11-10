import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# planar_necklace_two_cuts_refutation_of_instance

Topic: fair_division   Node: 6525fa4b4535

Provenance: helper lemma. arXiv:2610.27956 Conjecture 2

If there exists a finite planar point set P colored with red and blue counts divisible by 3 that admits no fair 3-agent division by at most 2 straight lines, then the universal two-cut splitting statement for 3 agents in the plane is false.
-/

/-- A single counterexample instance refutes the universal 2-cut planar necklace splitting statement for 3 agents. -/
theorem planar_necklace_two_cuts_refutation_of_instance
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2)
    (h_red : 3 ∣ (P.filter (fun p => c p = 0)).card)
    (h_blue : 3 ∣ (P.filter (fun p => c p = 1)).card)
    (h_nofair : ¬ ∃ (L : Finset StraightLine) (α : (ℝ × ℝ) → Fin 3),
      L.card ≤ 2 ∧
      is_straight_line_cut_consistent P L α ∧
      ∀ i : Fin 3,
        (P.filter (fun p => α p = i ∧ c p = 0)).card = (P.filter (fun p => c p = 0)).card / 3 ∧
        (P.filter (fun p => α p = i ∧ c p = 1)).card = (P.filter (fun p => c p = 1)).card / 3) :
    ¬ (∀ (P' : Finset (ℝ × ℝ)) (c' : (ℝ × ℝ) → Fin 2),
      3 ∣ (P'.filter (fun p => c' p = 0)).card →
      3 ∣ (P'.filter (fun p => c' p = 1)).card →
      ∃ (L : Finset StraightLine) (α : (ℝ × ℝ) → Fin 3),
        L.card ≤ 2 ∧
        is_straight_line_cut_consistent P' L α ∧
        ∀ i : Fin 3,
          (P'.filter (fun p => α p = i ∧ c' p = 0)).card = (P'.filter (fun p => c' p = 0)).card / 3 ∧
          (P'.filter (fun p => α p = i ∧ c' p = 1)).card = (P'.filter (fun p => c' p = 1)).card / 3) := by
  intro h
  exact h_nofair (h P c h_red h_blue)
