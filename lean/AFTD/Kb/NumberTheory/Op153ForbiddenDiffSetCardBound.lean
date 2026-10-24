import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153WitnessIndexBound
import AFTD.Kb.NumberTheory.Op153PositiveQuadraticSublevelCardBound

/-!
# op_153_forbidden_diff_set_card_bound

Topic: elementary_number_theory   Node: 9e0c87a5064c

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

For a degree-2 integer polynomial g strictly positive on the positive integers, any finite set of integers in {1, ..., N} each of which is a value g(n) with n > 0 has at most C*sqrt(N) elements, for large N.
-/

/-- The forbidden difference set is thin: the values of g taken in {1, \u2026, N} number only O(\u221aN), because each such value has a witness index n \u2264 N and distinct values have distinct witnesses. -/
theorem op_153_forbidden_diff_set_card_bound (g : Polynomial ℤ)
    (hdeg : g.degree = 2) (hpos : ∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ)) :
    ∃ C > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ T : Finset ℤ, (∀ d ∈ T, 0 < d ∧ d ≤ (N : ℤ) ∧ ∃ n : ℕ, 0 < n ∧ g.eval (n : ℤ) = d) →
      (T.card : ℝ) ≤ C * Real.sqrt (N : ℝ) := by
  classical
  obtain ⟨C, hC, N0, hbound⟩ := op_153_positive_quadratic_sublevel_card_bound g hdeg hpos
  obtain ⟨N1, hwit⟩ := op_153_witness_index_bound g hdeg hpos
  refine ⟨C, hC, max N0 N1, ?_⟩
  intro N hN T hT
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N1 ≤ N := le_trans (le_max_right _ _) hN
  let w : ℤ → ℕ := fun d => if hd : d ∈ T then Classical.choose (hT d hd).2.2 else 0
  have hwpos : ∀ d (hd : d ∈ T), 0 < w d := by
    intro d hd
    simp only [w, dif_pos hd]
    exact (Classical.choose_spec (hT d hd).2.2).1
  have hweq : ∀ d (hd : d ∈ T), g.eval ((w d : ℕ) : ℤ) = d := by
    intro d hd
    simp only [w, dif_pos hd]
    exact (Classical.choose_spec (hT d hd).2.2).2
  have hinj : Set.InjOn (fun d : ℤ => w d) ↑T := by
    intro d1 hd1 d2 hd2 heq
    have e1 := hweq d1 hd1
    have e2 := hweq d2 hd2
    rw [← e1, ← e2]
    exact congrArg (fun n : ℕ => g.eval (n : ℤ)) heq
  have hsub : T.image (fun d : ℤ => w d) ⊆
      (Finset.Icc 1 N).filter (fun n : ℕ => g.eval (n : ℤ) ≤ (N : ℤ)) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨d, hd, rfl⟩ := hn
    have hdT := hT d hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := hwpos d hd; omega
    · exact hwit N hN1 (w d) (hwpos d hd) (by rw [hweq d hd]; exact hdT.2.1)
    · rw [hweq d hd]; exact hdT.2.1
  have hcard : (T.image (fun d : ℤ => w d)).card = T.card := Finset.card_image_of_injOn hinj
  have hle : T.card ≤
      ((Finset.Icc 1 N).filter (fun n : ℕ => g.eval (n : ℤ) ≤ (N : ℤ))).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  calc (T.card : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun n : ℕ => g.eval (n : ℤ) ≤ (N : ℤ))).card : ℝ) := by
          exact_mod_cast hle
    _ ≤ C * Real.sqrt (N : ℝ) := hbound N hN0
