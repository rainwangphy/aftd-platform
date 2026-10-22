import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded

/-!
# op_258_card_fiber_tail_le

Topic: combinatorics   Node: 1db751810c46

Provenance: helper lemma. step towards op_258_forces_step

For an a-bounded colouring c of the edges of K_n, the number of edges with colour index strictly greater than C is at most the sum of a_i over colours used exceeding C multiplied by C(n, 2).
-/

/-- For an a-bounded colouring c of K_n, the number of edges coloured with index strictly greater than C is bounded by (∑_{i used, i > C} a_i) * C(n, 2). -/
theorem op_258_card_fiber_tail_le (a : ℕ+ → ℝ) (n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) (hc : op_258_bounded a n c)
    (C : ℕ) :
    (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter
      (fun e => C < (c e : ℕ))).card : ℝ) ≤
      (∑ i ∈ (Finset.univ.image c).filter (fun (i : ℕ+) => C < (i : ℕ)), a i) * (n.choose 2 : ℝ) := by
  let E := (SimpleGraph.completeGraph (Fin n)).edgeSet
  let s : Finset E := Finset.univ.filter (fun e => C < (c e : ℕ))
  let t : Finset ℕ+ := (Finset.univ.image c).filter (fun (i : ℕ+) => C < (i : ℕ))
  have hmaps : Set.MapsTo c (↑s : Set E) (↑t : Set ℕ+) := by
    intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_image_of_mem c (Finset.mem_univ e), he.2⟩
  have hfiber : s.card = ∑ i ∈ t, (s.filter (fun e => c e = i)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber_eq : ∀ i ∈ t, (s.filter (fun e => c e = i)) =
      ((Finset.univ : Finset E).filter (fun e => c e = i)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨?_, h⟩
      show e ∈ s
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h]
      exact hi.2
  have hfiber_real : (s.card : ℝ) =
      ∑ i ∈ t, (((Finset.univ : Finset E).filter (fun e => c e = i)).card : ℝ) := by
    rw [hfiber]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hfiber_eq i hi]
  rw [hfiber_real]
  have hle : (∑ i ∈ t, (((Finset.univ : Finset E).filter (fun e => c e = i)).card : ℝ)) ≤
      ∑ i ∈ t, (a i * (n.choose 2 : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hc i
  rw [← Finset.sum_mul] at hle
  exact hle
