import AFTD.Prelude
import AFTD.Kb.Tcs.RandicIndex

/-!
# op1012_complete_bipartite_randic_index

Topic: graphs   Node: 049c889c33cd

Provenance: formalization of a published result. Source: arXiv:2611.03879 Conjecture 3 text

For any positive integers a and b, the Randić index of the complete bipartite graph completeBipartiteGraph (Fin a) (Fin b) equals Real.sqrt ((a : ℝ) * (b : ℝ)).
-/

attribute [local instance] Classical.propDecidable in
/-- The Randić index of the complete bipartite graph K_{a,b} equals sqrt(a * b). -/
theorem op1012_complete_bipartite_randic_index
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    randic_index (completeBipartiteGraph (Fin a) (Fin b)) = Real.sqrt ((a : ℝ) * (b : ℝ)) := by
  classical
  letI : DecidableRel (completeBipartiteGraph (Fin a) (Fin b)).Adj := fun x y => Classical.propDecidable _
  have hdeg_inl : ∀ i : Fin a, (completeBipartiteGraph (Fin a) (Fin b)).degree (Sum.inl i) = b := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have h : (completeBipartiteGraph (Fin a) (Fin b)).neighborFinset (Sum.inl i)
        = (Finset.univ : Finset (Fin b)).image Sum.inr := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hw
        rw [completeBipartiteGraph_adj] at hw
        cases w with
        | inl x => simp at hw
        | inr y => exact ⟨y, rfl⟩
      · rintro ⟨j, rfl⟩
        rw [completeBipartiteGraph_adj]
        simp
    rw [h, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
      Fintype.card_fin]
  have hdeg_inr : ∀ j : Fin b, (completeBipartiteGraph (Fin a) (Fin b)).degree (Sum.inr j) = a := by
    intro j
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have h : (completeBipartiteGraph (Fin a) (Fin b)).neighborFinset (Sum.inr j)
        = (Finset.univ : Finset (Fin a)).image Sum.inl := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hw
        rw [completeBipartiteGraph_adj] at hw
        cases w with
        | inl x => exact ⟨x, rfl⟩
        | inr y => simp at hw
      · rintro ⟨i, rfl⟩
        rw [completeBipartiteGraph_adj]
        simp
    rw [h, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ,
      Fintype.card_fin]
  rw [randic_index]
  refine Eq.trans (Finset.sum_bij (s := (Finset.univ : Finset (Fin a × Fin b)))
    (f := fun p => Sym2.lift ⟨fun u v => 1 / Real.sqrt (((completeBipartiteGraph (Fin a) (Fin b)).degree u : ℝ) * ((completeBipartiteGraph (Fin a) (Fin b)).degree v : ℝ)), by intro u v; simp [mul_comm]⟩ s(Sum.inl p.1, Sum.inr p.2))
    (fun p _ => s(Sum.inl p.1, Sum.inr p.2)) ?_ ?_ ?_ ?_).symm ?_
  · intro p _
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_completeBipartiteGraph]
    exact ⟨p, rfl⟩
  · intro p _ q _ hpq
    rw [Sym2.eq, Sym2.rel_iff] at hpq
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
    · exact absurd h1 Sum.inl_ne_inr
  · intro e he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_completeBipartiteGraph] at he
    obtain ⟨p, hp⟩ := he
    exact ⟨p, Finset.mem_univ _, hp⟩
  · intro p _
    rfl
  · simp only [Sym2.lift_mk]
    have hterm : ∀ x : Fin a × Fin b,
        (1 : ℝ) / Real.sqrt ((↑((completeBipartiteGraph (Fin a) (Fin b)).degree (Sum.inl x.1)) : ℝ) * ↑((completeBipartiteGraph (Fin a) (Fin b)).degree (Sum.inr x.2))) = 1 / Real.sqrt ((a:ℝ)*(b:ℝ)) := by
      intro x
      rw [hdeg_inl, hdeg_inr, mul_comm]
    simp only [hterm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    have ha' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
    have hb' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
    have hab : (0:ℝ) < (a:ℝ) * (b:ℝ) := mul_pos ha' hb'
    have hsq := Real.sq_sqrt (le_of_lt hab)
    push_cast
    field_simp
    nlinarith [hsq]
