import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsDirectedPath
import AFTD.Kb.Tcs.DigraphIsDirectedPathSingleton

/-!
# digraph_finite_sink_strong_subgraph

Topic: graphs   Node: 7a3475defbf9

Provenance: helper lemma. Finite directed sink-component fact used in the oriented twenty-cut profile.

Every nonempty finite vertex set contains a nonempty strongly connected subset with no outgoing arc to the rest of that set.
-/

lemma digraph_finite_sink_strong_subgraph_path_extend_or_prefix
    {α : Type*} [DecidableEq α] (D : Digraph α) (T : Finset α)
    (u x y : α) (p : List α)
    (hp : digraph_is_directed_path D p u x) (hpT : ∀ z ∈ p, z ∈ T)
    (hyT : y ∈ T) (hadj : D.Adj x y) :
    ∃ q : List α, digraph_is_directed_path D q u y ∧ ∀ z ∈ q, z ∈ T := by
  by_cases hy : y ∈ p
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hy
    have hpref : l₁ ++ [y] <+: l₁ ++ y :: l₂ := ⟨l₂, by simp⟩
    refine ⟨l₁ ++ [y], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hp.1.prefix hpref
    · exact hp.2.1.sublist hpref.sublist
    · cases l₁ with
      | nil =>
        simp only [List.nil_append, List.head?_cons] at hp ⊢
        exact hp.2.2.1
      | cons w ws =>
        simp only [List.cons_append, List.head?_cons] at hp ⊢
        exact hp.2.2.1
    · simp
    · intro z hz
      exact hpT z (hpref.subset hz)
  · rcases hp with ⟨hchain, hnodup, hhead, hlast⟩
    have hp_ne : p ≠ [] := by
      rintro rfl
      simp at hhead
    refine ⟨p ++ [y], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · apply List.IsChain.append hchain (List.IsChain.singleton y)
      intro a ha b hb
      simp only [hlast, Option.mem_some_iff] at ha
      simp only [List.head?_cons, Option.mem_some_iff] at hb
      subst ha hb
      exact hadj
    · rw [List.nodup_append]
      refine ⟨hnodup, List.nodup_singleton y, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hy ha
    · rw [List.head?_append_of_ne_nil _ hp_ne]
      exact hhead
    · rw [List.getLast?_append_cons]
      simp
    · intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hpT z hz
      · exact hyT

theorem digraph_finite_sink_strong_subgraph
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (H : Finset α) (hne : H.Nonempty) :
    ∃ T : Finset α, T ⊆ H ∧ T.Nonempty ∧
      (∀ x ∈ T, ∀ y ∈ H, D.Adj x y → y ∈ T) ∧
      (∀ u ∈ T, ∀ v ∈ T,
        ∃ p : List α, digraph_is_directed_path D p u v ∧ ∀ z ∈ p, z ∈ T) := by
  classical
  let closed_subsets : Finset (Finset α) :=
    H.powerset.filter (fun S => S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ H, D.Adj x y → y ∈ S)
  have hH_mem : H ∈ closed_subsets := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset_self H, hne, fun x hx y hy _ => hy⟩
  have hcs_ne : closed_subsets.Nonempty := ⟨H, hH_mem⟩
  obtain ⟨T, hT_mem, hT_min⟩ := Finset.exists_min_image closed_subsets Finset.card hcs_ne
  rw [Finset.mem_filter, Finset.mem_powerset] at hT_mem
  rcases hT_mem with ⟨hTH, hTne, hTclosed⟩
  refine ⟨T, hTH, hTne, hTclosed, ?_⟩
  intro u hu v hv
  let R_u := T.filter (fun w => ∃ p : List α, digraph_is_directed_path D p u w ∧ ∀ z ∈ p, z ∈ T)
  have hu_Ru : u ∈ R_u := by
    rw [Finset.mem_filter]
    refine ⟨hu, [u], digraph_is_directed_path_singleton D u, ?_⟩
    intro z hz
    simp only [List.mem_singleton] at hz
    subst hz
    exact hu
  have hRu_ne : R_u.Nonempty := ⟨u, hu_Ru⟩
  have hRu_sub_T : R_u ⊆ T := Finset.filter_subset _ _
  have hRu_sub_H : R_u ⊆ H := hRu_sub_T.trans hTH
  have hRu_closed : ∀ x ∈ R_u, ∀ y ∈ H, D.Adj x y → y ∈ R_u := by
    intro x hx y hy hadj
    rw [Finset.mem_filter] at hx
    rcases hx with ⟨hxT, p, hp, hpT⟩
    have hyT : y ∈ T := hTclosed x hxT y hy hadj
    obtain ⟨q, hq, hqT⟩ :=
      digraph_finite_sink_strong_subgraph_path_extend_or_prefix D T u x y p hp hpT hyT hadj
    rw [Finset.mem_filter]
    exact ⟨hyT, q, hq, hqT⟩
  have hRu_mem : R_u ∈ closed_subsets := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hRu_sub_H, hRu_ne, hRu_closed⟩
  have hcard_le : T.card ≤ R_u.card := hT_min R_u hRu_mem
  have hT_eq_Ru : T = R_u := Finset.Subset.antisymm
    (Finset.eq_of_subset_of_card_le hRu_sub_T hcard_le ▸ subset_rfl)
    hRu_sub_T
  have hv_Ru : v ∈ R_u := hT_eq_Ru ▸ hv
  rw [Finset.mem_filter] at hv_Ru
  exact hv_Ru.2
