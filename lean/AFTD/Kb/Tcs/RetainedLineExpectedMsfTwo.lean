import AFTD.Prelude
import AFTD.Kb.Tcs.RetainedLineExpectedMsf
import AFTD.Kb.Tcs.RetainedLineMsfWeightEmpty
import AFTD.Kb.Tcs.RetainedLineMsfWeight
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.GraphCost
import AFTD.Kb.Tcs.Support
import AFTD.Kb.Tcs.F

/-!
# retained_line_expected_msf_two

Topic: algorithms   Node: 7affa52b1c52

Provenance: helper lemma. Sanity check for the independent-edge distribution in OP-815.

For two vertices, the expected retained minimum spanning forest weight is q.
-/

open scoped Classical
open Finset

lemma retained_line_expected_msf_two_simpleGraph_fin_two (G : SimpleGraph (Fin 2)) : G = ⊥ ∨ G = ⊤ := by
  by_cases h : G.Adj 0 1
  · right
    ext u v
    fin_cases u <;> fin_cases v
    · simp
    · simpa using h
    · simp [G.adj_symm h]
    · simp
  · left
    ext u v
    fin_cases u <;> fin_cases v
    · simp
    · simp [h]
    · simp [mt G.adj_symm h]
    · simp

lemma retained_line_expected_msf_two_bot_ne_top : (⊥ : SimpleGraph (Fin 2)) ≠ ⊤ := by
  intro h
  have := congr_fun₂ (congr_arg SimpleGraph.Adj h) 0 1
  simp at this

lemma retained_line_expected_msf_two_univ : (Finset.univ : Finset (SimpleGraph (Fin 2))) = {⊥, ⊤} := by
  ext G
  simp only [mem_univ, true_iff, mem_insert, mem_singleton]
  exact retained_line_expected_msf_two_simpleGraph_fin_two G

lemma retained_line_expected_msf_two_top_acyclic : (⊤ : SimpleGraph (Fin 2)).IsAcyclic := by
  intro v c hc
  have h3 := hc.three_le_length
  have hle : c.support.tail.length ≤ 2 := List.Nodup.length_le_card hc.support_nodup
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support, Nat.add_sub_cancel]
  omega

lemma retained_line_expected_msf_two_msf_weight_top :
    retained_line_msf_weight (⊤ : SimpleGraph (Fin 2)) = 1 := by
  simp only [retained_line_msf_weight]
  have h : {x : ℝ | ∃ F : SimpleGraph (Fin 2),
    Maximal (fun H : SimpleGraph (Fin 2) => H ≤ ⊤ ∧ H.IsAcyclic) F ∧
    x = graph_cost (fun i j => |(i.val : ℝ) - (j.val : ℝ)|) F} = {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨F, hF, rfl⟩
      have hf : F = ⊤ := by
        apply le_antisymm le_top
        exact hF.2 ⟨le_rfl, retained_line_expected_msf_two_top_acyclic⟩ le_top
      subst F
      simp [graph_cost, Fin.sum_univ_two]
      ring
    · intro hx
      subst x
      refine ⟨⊤, ?_, ?_⟩
      · refine ⟨⟨le_rfl, retained_line_expected_msf_two_top_acyclic⟩, ?_⟩
        intro b hb _
        exact hb.1
      · simp [graph_cost, Fin.sum_univ_two]
        ring
  rw [h, csInf_singleton]

lemma retained_line_expected_msf_two_card_edgeFinset_top :
  @Finset.card (Sym2 (Fin 2))
    (@SimpleGraph.edgeFinset (Fin 2) ⊤
      (@SimpleGraph.fintypeEdgeSet (Fin 2) ⊤ Sym2.instFintype
        fun a b => Classical.propDecidable (SimpleGraph.Adj ⊤ a b))) = 1 := by
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card]
  let inst1 := @SimpleGraph.fintypeEdgeSet (Fin 2) ⊤ Sym2.instFintype
    (fun a b => Classical.propDecidable (SimpleGraph.Adj ⊤ a b))
  let inst2 := @SimpleGraph.fintypeEdgeSet (Fin 2) ⊤ Sym2.instFintype
    (fun a b => @SimpleGraph.Top.adjDecidable (Fin 2) _ a b)
  have h_eq : @Fintype.card (⊤ : SimpleGraph (Fin 2)).edgeSet inst1 =
              @Fintype.card (⊤ : SimpleGraph (Fin 2)).edgeSet inst2 :=
    @Fintype.card_congr _ _ inst1 inst2 (Equiv.refl _)
  change @Fintype.card (⊤ : SimpleGraph (Fin 2)).edgeSet inst1 = 1
  rw [h_eq]
  have h2 : @Fintype.card (⊤ : SimpleGraph (Fin 2)).edgeSet inst2 = 1 := by
    have h_choose := @SimpleGraph.card_edgeFinset_top_eq_card_choose_two (Fin 2) _ _
    rw [← @Set.toFinset_card (Sym2 (Fin 2)) (⊤ : SimpleGraph (Fin 2)).edgeSet inst2]
    exact h_choose
  exact h2

theorem retained_line_expected_msf_two (q : ℝ) : retained_line_expected_msf 2 q = q := by
  unfold retained_line_expected_msf
  rw [retained_line_expected_msf_two_univ]
  rw [Finset.sum_pair retained_line_expected_msf_two_bot_ne_top]
  rw [retained_line_msf_weight_empty, retained_line_expected_msf_two_msf_weight_top]
  simp only [mul_zero, zero_add, mul_one]
  rw [retained_line_expected_msf_two_card_edgeFinset_top]
  norm_num
