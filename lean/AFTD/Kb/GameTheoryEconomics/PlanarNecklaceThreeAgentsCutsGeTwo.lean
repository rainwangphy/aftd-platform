import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent
import AFTD.Kb.GameTheoryEconomics.NotIsStraightLineCutConsistentSingletonOfThreeAgents

/-!
# planar_necklace_three_agents_cuts_ge_two

Topic: fair_division   Node: 5816d5dbbb69

Provenance: helper lemma. arXiv:2610.27956 Proposition 1 (Splitting Planar Necklaces with Few Straight Cuts)

Let P be a finite set of points in ℝ × ℝ colored with two colors c : (ℝ × ℝ) → Fin 2, L a finite set of straight lines, and α an allocation function from ℝ × ℝ to Fin 3. If each of the three agents receives exactly 1 point of color 0 and 1 point of color 1 from P, and α is consistent with L on P, then L contains at least 2 straight lines.
-/

/-- Tightness of Conjecture 2: any fair allocation among three agents receiving at least one point of each color requires at least two straight lines. -/
theorem planar_necklace_three_agents_cuts_ge_two
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2) (L : Finset StraightLine)
    (α : (ℝ × ℝ) → Fin 3)
    (h_fair : ∀ i : Fin 3,
      (P.filter (fun p => α p = i ∧ c p = 0)).card = 1 ∧
      (P.filter (fun p => α p = i ∧ c p = 1)).card = 1)
    (h_cons : is_straight_line_cut_consistent P L α) :
    2 ≤ L.card := by
  classical
  have h_surj : ∀ i : Fin 3, ∃ p ∈ P, α p = i := by
    intro i
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 (h_fair i).1
    have hmem : p ∈ P.filter (fun p => α p = i ∧ c p = 0) := by rw [hp]; simp
    rw [Finset.mem_filter] at hmem
    exact ⟨p, hmem.1, hmem.2.1⟩
  by_contra h
  have hc : L.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h0 | h1
  · have hL : L = ∅ := Finset.card_eq_zero.1 h0
    rw [hL] at h_cons
    obtain ⟨s, hs_cut, hs_α⟩ := h_cons
    obtain ⟨p₀, hp₀, hα₀⟩ := h_surj 0
    obtain ⟨p₁, hp₁, hα₁⟩ := h_surj 1
    have heq : (0 : Fin 3) = 1 := by
      rw [← hα₀, ← hα₁]
      exact hs_α p₀ hp₀ p₁ hp₁ (by intro ℓ hℓ; simp at hℓ)
    exact absurd heq (by decide)
  · obtain ⟨ℓ, rfl⟩ := Finset.card_eq_one.1 h1
    exact not_is_straight_line_cut_consistent_singleton_of_three_agents P ℓ α h_surj h_cons
