import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDegenerate
import AFTD.Kb.Tcs.Support

/-!
# tree_edge_disjoint_embedding_of_star_T

Topic: graphs   Node: 3683ee4dc96e

Provenance: helper lemma. arXiv:2611.04674 Lemma 2.1 (Pair preparation)

For n ≥ 2, if T is a spanning star tree on Fin n with center r, then every tree S on Fin (n - 1) can be embedded into Fin n edge-disjointly from T such that the union graph T ⊔ S.map φ is 2-degenerate.
-/

open SimpleGraph

lemma tree_edge_disjoint_embedding_of_star_T_forest_exists_deg_le_one {V : Type*} [Finite V]
    (H : SimpleGraph V) (hH : H.IsAcyclic) {s : Set V} (hs : s.Nonempty) :
    ∃ v ∈ s, (s ∩ H.neighborSet v).encard ≤ 1 := by
  classical
  haveI : Nonempty s := hs.to_subtype
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length (H.induce s)
  have hacyc : (H.induce s).IsAcyclic := hH.induce s
  refine ⟨u.1, u.2, ?_⟩
  have hsub : (s ∩ H.neighborSet u.1) ⊆ {p.snd.1} := by
    intro x hx
    obtain ⟨hxs, hxadj⟩ := hx
    have hadj : (H.induce s).Adj u ⟨x, hxs⟩ := by
      rw [SimpleGraph.induce_adj]; exact hxadj
    by_cases hmem : (⟨x, hxs⟩ : s) ∈ p.support
    · have := hacyc.eq_snd_of_adj_start hp hadj hmem
      simp only [Set.mem_singleton_iff]
      exact congrArg Subtype.val this
    · have hpath : (SimpleGraph.Walk.cons hadj.symm p).IsPath := hp.cons hmem
      have := hmax _ _ _ hpath
      rw [SimpleGraph.Walk.length_cons] at this
      omega
  calc (s ∩ H.neighborSet u.1).encard ≤ ({p.snd.1} : Set V).encard := Set.encard_mono hsub
    _ = 1 := Set.encard_singleton _

/-- When the host spanning tree is a star, any tree of order n-1 can be packed edge-disjointly with 2-degenerate union. -/
theorem tree_edge_disjoint_embedding_of_star_T {n : ℕ} (hn : 2 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) (r : Fin n) (hTr : T = SimpleGraph.starGraph r)
    (S : SimpleGraph (Fin (n - 1))) (hS : S.IsTree) :
    ∃ φ : Fin (n - 1) ↪ Fin n,
      Disjoint T (S.map φ) ∧ simple_graph_is_degenerate (T ⊔ S.map φ) 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hTr
  let Φ : Fin m ↪ Fin (m + 1) := ⟨fun i => r.succAbove i, Fin.succAbove_right_injective⟩
  have hΦ : ∀ i, Φ i = r.succAbove i := fun i => rfl
  refine ⟨Φ, ?_, ?_⟩
  · rw [disjoint_iff_inf_le, SimpleGraph.le_iff_adj]
    intro u v huv
    exfalso
    rw [SimpleGraph.inf_adj, SimpleGraph.starGraph_adj, SimpleGraph.map_adj] at huv
    obtain ⟨⟨-, hru | hrv⟩, ⟨a, b, -, ha, hb⟩⟩ := huv
    · refine Fin.succAbove_ne r a ?_
      show Φ a = r
      rw [ha, hru]
    · refine Fin.succAbove_ne r b ?_
      show Φ b = r
      rw [hb, hrv]
  · intro s hs
    by_cases hcase : ∃ x ∈ s, x ≠ r
    · obtain ⟨x, hxs, hxr⟩ := hcase
      have hxrange : x ∈ Set.range (fun i => r.succAbove i) := by
        rw [Fin.range_succAbove]; simpa using hxr
      obtain ⟨i, hi⟩ := hxrange
      have hsi : i ∈ Φ ⁻¹' s := by
        show (fun i => r.succAbove i) i ∈ s
        rw [hi]; exact hxs
      obtain ⟨j, hjt, hjc⟩ := tree_edge_disjoint_embedding_of_star_T_forest_exists_deg_le_one
        S hS.isAcyclic (s := Φ ⁻¹' s) ⟨i, hsi⟩
      have hjt' : Φ j ∈ s := hjt
      refine ⟨Φ j, hjt', ?_⟩
      have hsub : s ∩ (starGraph r ⊔ S.map Φ).neighborSet (Φ j)
          ⊆ insert r (Φ '' (Φ ⁻¹' s ∩ S.neighborSet j)) := by
        intro y hy
        obtain ⟨hys, hyadj⟩ := hy
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj] at hyadj
        rcases hyadj with hstar | hmap
        · rw [SimpleGraph.starGraph_adj] at hstar
          obtain ⟨-, h1 | h2⟩ := hstar
          · exact absurd (by rw [← hΦ j]; exact h1) (Fin.succAbove_ne r j)
          · exact Set.mem_insert_iff.mpr (Or.inl h2)
        · rw [SimpleGraph.map_adj] at hmap
          obtain ⟨a, b, hab, ha, hb⟩ := hmap
          have haj : a = j := Fin.succAbove_right_injective
            (show r.succAbove a = r.succAbove j by rw [← hΦ a, ← hΦ j]; exact ha)
          refine Set.mem_insert_iff.mpr (Or.inr ⟨b, ⟨?_, ?_⟩, hb⟩)
          · rw [Set.mem_preimage, hb]; exact hys
          · rw [haj] at hab; exact hab
      have hnotmem : r ∉ Φ '' (Φ ⁻¹' s ∩ S.neighborSet j) := by
        rintro ⟨b, -, hb⟩
        refine Fin.succAbove_ne r b ?_
        show Φ b = r
        exact hb
      have henc : (Φ '' (Φ ⁻¹' s ∩ S.neighborSet j)).encard
          = (Φ ⁻¹' s ∩ S.neighborSet j).encard :=
        Function.Injective.encard_image Φ.injective _
      calc (s ∩ (starGraph r ⊔ S.map Φ).neighborSet (Φ j)).encard
          ≤ (insert r (Φ '' (Φ ⁻¹' s ∩ S.neighborSet j))).encard := Set.encard_mono hsub
        _ = (Φ '' (Φ ⁻¹' s ∩ S.neighborSet j)).encard + 1 :=
            Set.encard_insert_of_notMem hnotmem
        _ = (Φ ⁻¹' s ∩ S.neighborSet j).encard + 1 := by rw [henc]
        _ ≤ 1 + 1 := add_le_add hjc le_rfl
        _ = ((2 : ℕ) : ℕ∞) := by norm_num
    · push Not at hcase
      obtain ⟨x, hx⟩ := hs
      have hrs : r ∈ s := by rw [← hcase x hx]; exact hx
      refine ⟨r, hrs, ?_⟩
      have hemp : s ∩ (starGraph r ⊔ S.map Φ).neighborSet r = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨hys, hyN⟩
        rw [SimpleGraph.mem_neighborSet] at hyN
        exact (SimpleGraph.loopless _).irrefl r (hcase y hys ▸ hyN)
      rw [hemp]
      exact Set.encard_empty.le.trans (by simp)
