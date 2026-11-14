import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SupportGraph
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# op_1628_p3_consecutive_equality

Topic: combinatorics   Node: 7245d6a1a6c1

Provenance: helper lemma. arXiv:2611.15376 Question 7.1

The set-coloring Ramsey numbers for the path graph pathGraph 3 with palette parameters r = 4 and s = 3 satisfy set_coloring_ramsey_number (SimpleGraph.pathGraph 3) 4 3 1 = set_coloring_ramsey_number (SimpleGraph.pathGraph 3) 4 3 2.
-/

open scoped Classical in
private lemma op_1628_p3_consecutive_equality_cherry
    (ϕ : ↑(⊤ : SimpleGraph (Fin 3)).edgeSet → Finset (Fin 4))
    (hϕ : ∀ e, (ϕ e).card = 3) (t : ℕ) (ht : t ≤ 2) :
    ∃ T : Finset (Fin 4), T.card = t ∧
      (SimpleGraph.pathGraph 3).IsContained (support_graph ϕ T) := by
  classical
  have hall : ∀ u v : Fin 3, (SimpleGraph.pathGraph 3).Adj u v →
      s(u,v) = s(0,1) ∨ s(u,v) = s(1,2) := by
    intro u v huv
    rw [SimpleGraph.pathGraph_adj] at huv
    fin_cases u <;> fin_cases v <;> simp_all
  set e1 : ↑(⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(0,1), by simp⟩ with he1
  set e2 : ↑(⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(1,2), by simp⟩ with he2
  have hcard : 2 ≤ (ϕ e1 ∩ ϕ e2).card := by
    have h1 : (ϕ e1).card = 3 := hϕ e1
    have h2 : (ϕ e2).card = 3 := hϕ e2
    have hu : (ϕ e1 ∪ ϕ e2).card ≤ 4 := by
      have := Finset.card_le_univ (ϕ e1 ∪ ϕ e2)
      simpa using this
    have := Finset.card_union_add_card_inter (ϕ e1) (ϕ e2)
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := ϕ e1 ∩ ϕ e2) (n := t) (by omega)
  have hT1 : T ⊆ ϕ e1 := fun x hx => (Finset.mem_inter.mp (hTsub hx)).1
  have hT2 : T ⊆ ϕ e2 := fun x hx => (Finset.mem_inter.mp (hTsub hx)).2
  refine ⟨T, hTcard, ?_⟩
  refine ⟨⟨SimpleGraph.Hom.ofLE ?_, fun a b hab => hab⟩⟩
  intro u v huv
  simp only [support_graph, SimpleGraph.fromEdgeSet_adj]
  have hmem : s(u,v) ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet := by
    simpa using huv.ne
  refine ⟨⟨hmem, ?_⟩, huv.ne⟩
  rcases hall u v huv with h | h
  · have he : (⟨s(u,v), hmem⟩ : ↑(⊤ : SimpleGraph (Fin 3)).edgeSet) = e1 := Subtype.ext h
    rw [he]; exact hT1
  · have he : (⟨s(u,v), hmem⟩ : ↑(⊤ : SimpleGraph (Fin 3)).edgeSet) = e2 := Subtype.ext h
    rw [he]; exact hT2

open scoped Classical in
private lemma op_1628_p3_consecutive_equality_prop_three (t : ℕ) (ht : t ≤ 2) :
    set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t 3 := by
  intro ϕ hϕ
  exact op_1628_p3_consecutive_equality_cherry ϕ hϕ t ht

open scoped Classical in
private lemma op_1628_p3_consecutive_equality_not_prop_le_two (t N : ℕ) (hN : N ≤ 2) :
    ¬ set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t N := by
  classical
  intro hprop
  obtain ⟨T, -, ⟨copy⟩⟩ := hprop (fun _ => ({0,1,2} : Finset (Fin 4))) (fun e => by simp)
  have hinj : Function.Injective (fun i : Fin 3 => copy.toHom.toFun i) := copy.injective'
  have hc := Fintype.card_le_of_injective _ hinj
  simp at hc
  omega

open scoped Classical in
private lemma op_1628_p3_consecutive_equality_number_eq_three (t : ℕ) (ht : t ≤ 2) :
    set_coloring_ramsey_number (SimpleGraph.pathGraph 3) 4 3 t = 3 := by
  show sInf {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t N} = 3
  have h3 : (3:ℕ) ∈ {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t N} :=
    op_1628_p3_consecutive_equality_prop_three t ht
  refine le_antisymm (Nat.sInf_le h3) ?_
  have hmem : sInf {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t N} ∈
      {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t N} :=
    Nat.sInf_mem ⟨3, h3⟩
  have hnot : ¬ (sInf {N : ℕ | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) 4 3 t N} ≤ 2) :=
    fun h => op_1628_p3_consecutive_equality_not_prop_le_two t _ h hmem
  omega

/-- Equality of consecutive Ramsey numbers for the path P_3 at r = 4, s = 3, t = 1 and t = 2. -/
theorem op_1628_p3_consecutive_equality :
    set_coloring_ramsey_number (SimpleGraph.pathGraph 3) 4 3 1 =
    set_coloring_ramsey_number (SimpleGraph.pathGraph 3) 4 3 2 := by
  rw [op_1628_p3_consecutive_equality_number_eq_three 1 (by norm_num),
    op_1628_p3_consecutive_equality_number_eq_three 2 (by norm_num)]
