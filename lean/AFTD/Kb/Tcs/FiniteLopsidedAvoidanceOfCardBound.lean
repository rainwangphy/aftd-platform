import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteLopsidedFunctionProductBound

/-!
# finite_lopsided_avoidance_of_card_bound

Topic: graphs   Node: 0df4c11e4f36

Provenance: helper lemma. Finite-cardinality specialization of EJC 14 (2007) R63, DOI 10.37236/981, Lemma 3; helper for OP-306.

In a nonempty finite probability universe, finite bad events satisfying the negative-dependency cardinality inequalities and asymmetric weight inequalities can all be avoided.
-/

theorem finite_lopsided_avoidance_of_card_bound
    {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A : I → Finset Ω) (N : I → Finset I) (p x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hdep : ∀ i (S : Finset I), i ∉ S → Disjoint S (N i) →
      ((A i ∩ Finset.univ.filter (fun ω => ∀ j ∈ S, ω ∉ A j)).card : ℝ) ≤
        p i * ((Finset.univ.filter (fun ω => ∀ j ∈ S, ω ∉ A j)).card : ℝ))
    (hprob : ∀ i, p i ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∃ ω : Ω, ∀ i, ω ∉ A i := by
  classical
  let B : Finset I → Finset Ω := fun S => Finset.univ.filter (fun ω => ∀ j ∈ S, ω ∉ A j)
  have hB : ∀ i S, B (insert i S) = B S \ A i := by
    intro i S
    ext ω
    simp [B, and_comm]
  have hdiff : ∀ i S, ((B S).card : ℝ) - ((B (insert i S)).card : ℝ) =
      ((A i ∩ B S).card : ℝ) := by
    intro i S
    have hc := Finset.card_sdiff_add_card_inter (B S) (A i)
    rw [← hB, Finset.inter_comm] at hc
    have hc' : ((B (insert i S)).card : ℝ) + ((A i ∩ B S).card : ℝ) =
        ((B S).card : ℝ) := by exact_mod_cast hc
    linarith
  have hanti : ∀ S T, S ⊆ T → B T ⊆ B S := by
    intro S T hST ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun j hj => (Finset.mem_filter.mp hω).2 j (hST hj)⟩
  have hbound := finite_lopsided_function_product_bound
    (fun S => ((B S).card : ℝ)) N p x (fun _ => Nat.cast_nonneg _)
    (by
      intro i S T hST _
      rw [hdiff, hdiff]
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left (hanti S T hST)))
    (by intro i S hi hd; rw [hdiff]; exact hdep i S hi hd)
    hx0 hx1 hprob
  have hpos : 0 < (∏ i, (1 - x i)) * ((B ∅).card : ℝ) := by
    apply mul_pos
    · exact Finset.prod_pos (fun i _ => by linarith [hx1 i])
    · have he : B ∅ = Finset.univ := by ext ω; simp [B]
      rw [he, Finset.card_univ]
      exact_mod_cast Fintype.card_pos
  have hnon : (B Finset.univ).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_lt_of_le hpos hbound)
  obtain ⟨ω, hω⟩ := hnon
  exact ⟨ω, fun i => (Finset.mem_filter.mp hω).2 i (Finset.mem_univ _)⟩
