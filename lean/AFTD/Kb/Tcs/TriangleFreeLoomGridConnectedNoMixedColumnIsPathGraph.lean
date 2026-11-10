import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleFreeLoomGrid
import AFTD.Kb.Tcs.TriangleFreeLoomGridVert
import AFTD.Kb.Tcs.IsPathGraph

/-!
# triangle_free_loom_grid_connected_no_mixed_column_is_path_graph

Topic: graphs   Node: c65ebafb111c

Provenance: formalization of a published result. Source: arXiv:2611.09627 Lemma 3.1(a)

In a triangle-free loom grid T_{r,c}, every nonempty connected vertex set with no mixed column induces a path graph.
-/

/-- In a triangle-free loom grid, any nonempty connected vertex set with no mixed column induces a path graph. -/
theorem triangle_free_loom_grid_connected_no_mixed_column_is_path_graph
    {r c : ℕ} (U : Set (triangle_free_loom_grid_vert r c))
    (h_conn : ((triangle_free_loom_grid r c).induce U).Connected)
    (h_no_mix : ∀ j : Fin c, ¬ ((∃ u ∈ U, u.1.2.1 = j ∧ u.1.2.2 = false) ∧
      (∃ u ∈ U, u.1.2.1 = j ∧ u.1.2.2 = true))) :
    is_path_graph ((triangle_free_loom_grid r c).induce U) := by
  classical
  have : Fintype (triangle_free_loom_grid_vert r c) := by
    unfold triangle_free_loom_grid_vert
    infer_instance

  have no_same_col_adj : ∀ (u v : U), ((triangle_free_loom_grid r c).induce U).Adj u v → u.1.1.2.1 ≠ v.1.1.2.1 := by
    intro u v h_adj h_col
    have hadj' := h_adj
    rw [SimpleGraph.induce_adj, triangle_free_loom_grid, SimpleGraph.fromRel_adj] at hadj'
    rcases hadj'.2 with (⟨h1, h2, h3, -⟩ | ⟨h1, h2⟩) | (⟨h1, h2, h3, -⟩ | ⟨h1, h2⟩)
    · apply h_no_mix u.1.1.2.1
      refine ⟨⟨u.1, u.2, rfl, h2⟩, ⟨v.1, v.2, ?_, h3⟩⟩
      exact h1.symm
    · omega
    · apply h_no_mix v.1.1.2.1
      refine ⟨⟨v.1, v.2, rfl, h2⟩, ⟨u.1, u.2, ?_, h3⟩⟩
      exact h1.symm
    · omega

  have adj_row_eq_and_col_diff : ∀ (u v : U), ((triangle_free_loom_grid r c).induce U).Adj u v →
      u.1.1.1 = v.1.1.1 ∧ (u.1.1.2.1.val + 1 = v.1.1.2.1.val ∨ v.1.1.2.1.val + 1 = u.1.1.2.1.val) := by
    intro u v h_adj
    have hcol := no_same_col_adj u v h_adj
    have hadj' := h_adj
    rw [SimpleGraph.induce_adj, triangle_free_loom_grid, SimpleGraph.fromRel_adj] at hadj'
    rcases hadj'.2 with (⟨h1, -⟩ | ⟨h1, h2⟩) | (⟨h1, -⟩ | ⟨h1, h2⟩)
    · exact False.elim (hcol h1)
    · exact ⟨h1, Or.inl h2⟩
    · exact False.elim (hcol h1.symm)
    · exact ⟨h1.symm, Or.inr h2⟩

  have row_eq_of_walk : ∀ {u v : U}, ((triangle_free_loom_grid r c).induce U).Walk u v → u.1.1.1 = v.1.1.1 := by
    intro u v p
    induction p with
    | nil => rfl
    | cons hadj p ih =>
      have := adj_row_eq_and_col_diff _ _ hadj
      rw [this.1, ih]

  have col_inj : ∀ (u v : U), u.1.1.2.1 = v.1.1.2.1 → u = v := by
    intro u v hcol
    obtain ⟨p⟩ := h_conn.preconnected u v
    have hrow : u.1.1.1 = v.1.1.1 := row_eq_of_walk p
    have hbool : u.1.1.2.2 = v.1.1.2.2 := by
      by_contra h_diff
      apply h_no_mix u.1.1.2.1
      revert h_diff
      cases hu_b : u.1.1.2.2 <;> cases hv_b : v.1.1.2.2
      · intro h; exact False.elim (h rfl)
      · intro _
        refine ⟨⟨u.1, u.2, rfl, hu_b⟩, ⟨v.1, v.2, hcol.symm, hv_b⟩⟩
      · intro _
        refine ⟨⟨v.1, v.2, hcol.symm, hv_b⟩, ⟨u.1, u.2, rfl, hu_b⟩⟩
      · intro h; exact False.elim (h rfl)
    have h_val : u.1.1 = v.1.1 := by
      rcases u with ⟨⟨⟨u1, u2, u3⟩, hu_prop⟩, hu_mem⟩
      rcases v with ⟨⟨⟨v1, v2, v3⟩, hv_prop⟩, hv_mem⟩
      dsimp at *
      subst hrow hcol hbool
      rfl
    have h_u : u.1 = v.1 := Subtype.ext h_val
    exact Subtype.ext h_u

  have adj_iff : ∀ (u v : U), ((triangle_free_loom_grid r c).induce U).Adj u v ↔
      u.1.1.2.1.val + 1 = v.1.1.2.1.val ∨ v.1.1.2.1.val + 1 = u.1.1.2.1.val := by
    intro u v
    constructor
    · exact fun h => (adj_row_eq_and_col_diff u v h).2
    · intro h
      obtain ⟨p⟩ := h_conn.preconnected u v
      have hrow : u.1.1.1 = v.1.1.1 := row_eq_of_walk p
      have hne : u.1 ≠ v.1 := by
        intro heq
        have : u.1.1.2.1.val = v.1.1.2.1.val := by rw [heq]
        rcases h with h1 | h2 <;> omega
      rw [SimpleGraph.induce_adj, triangle_free_loom_grid, SimpleGraph.fromRel_adj]
      refine ⟨hne, ?_⟩
      rcases h with h1 | h2
      · left; right; exact ⟨hrow, h1⟩
      · right; right; exact ⟨hrow.symm, h2⟩

  have col_interval : ∀ (k : ℕ) (u_lt u_gt : U),
      u_lt.1.1.2.1.val ≤ k → k ≤ u_gt.1.1.2.1.val → ∃ u : U, u.1.1.2.1.val = k := by
    intro k u_lt u_gt hlt hgt
    by_contra h_none
    push Not at h_none
    have hlt' : u_lt.1.1.2.1.val < k := by
      have : u_lt.1.1.2.1.val ≠ k := fun h => h_none u_lt h
      omega
    have hgt' : k < u_gt.1.1.2.1.val := by
      have : u_gt.1.1.2.1.val ≠ k := fun h => h_none u_gt h
      omega
    let A : Set U := {u | u.1.1.2.1.val < k}
    have hA_lt : u_lt ∈ A := hlt'
    have hA_gt : u_gt ∉ A := by simp [A]; omega
    obtain ⟨p⟩ := h_conn.preconnected u_lt u_gt
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart A hA_lt hA_gt
    have hadj := d.adj
    rw [adj_iff] at hadj
    have hd1_lt : d.fst.1.1.2.1.val < k := hd1
    have hd2_ge : k < d.snd.1.1.2.1.val := by
      have hnot : ¬ d.snd.1.1.2.1.val < k := hd2
      have hne : d.snd.1.1.2.1.val ≠ k := fun h => h_none d.snd h
      omega
    rcases hadj with h1 | h2 <;> omega

  let S : Finset ℕ := Finset.image (fun u : U => u.1.1.2.1.val) Finset.univ
  have hSne : S.Nonempty := by
    obtain ⟨u0⟩ := h_conn.nonempty
    exact ⟨u0.1.1.2.1.val, Finset.mem_image.2 ⟨u0, Finset.mem_univ _, rfl⟩⟩
  let m := S.min' hSne
  let M := S.max' hSne
  obtain ⟨u_min, -, hu_min⟩ := Finset.mem_image.1 (Finset.min'_mem S hSne)
  obtain ⟨u_max, -, hu_max⟩ := Finset.mem_image.1 (Finset.max'_mem S hSne)
  have hmle : m ≤ M := Finset.min'_le S M (Finset.max'_mem S hSne)
  let n := M - m + 1
  have hrng : ∀ u : U, m ≤ u.1.1.2.1.val ∧ u.1.1.2.1.val < m + n := by
    intro u
    have hu : u.1.1.2.1.val ∈ S := Finset.mem_image.2 ⟨u, Finset.mem_univ _, rfl⟩
    have hm := Finset.min'_le S _ hu
    have hM := Finset.le_max' S _ hu
    exact ⟨hm, by omega⟩

  let f : U → Fin n := fun u => ⟨u.1.1.2.1.val - m, by
    have := (hrng u).2
    have := (hrng u).1
    omega⟩

  have f_inj : Function.Injective f := by
    intro u v huv
    simp only [f, Fin.mk.injEq] at huv
    have hu := (hrng u).1
    have hv := (hrng v).1
    have heq : u.1.1.2.1.val = v.1.1.2.1.val := by omega
    exact col_inj u v (Fin.ext heq)

  have f_surj : Function.Surjective f := by
    intro ⟨i, hi⟩
    have h1 : u_min.1.1.2.1.val ≤ m + i := by rw [hu_min]; omega
    have h2 : m + i ≤ u_max.1.1.2.1.val := by rw [hu_max]; omega
    obtain ⟨u, hu⟩ := col_interval (m + i) u_min u_max h1 h2
    refine ⟨u, ?_⟩
    ext
    simp only [f]
    omega

  let e : U ≃ Fin n := Equiv.ofBijective f ⟨f_inj, f_surj⟩
  have e_adj : ∀ a b : U, (SimpleGraph.pathGraph n).Adj (e a) (e b) ↔
      ((triangle_free_loom_grid r c).induce U).Adj a b := by
    intro a b
    rw [SimpleGraph.pathGraph_adj, adj_iff]
    have ha := (hrng a).1
    have hb := (hrng b).1
    change (e a).val + 1 = (e b).val ∨ (e b).val + 1 = (e a).val ↔
      a.1.1.2.1.val + 1 = b.1.1.2.1.val ∨ b.1.1.2.1.val + 1 = a.1.1.2.1.val
    change (a.1.1.2.1.val - m) + 1 = (b.1.1.2.1.val - m) ∨ (b.1.1.2.1.val - m) + 1 = (a.1.1.2.1.val - m) ↔
      a.1.1.2.1.val + 1 = b.1.1.2.1.val ∨ b.1.1.2.1.val + 1 = a.1.1.2.1.val
    constructor
    · rintro (h | h) <;> [left; right] <;> omega
    · rintro (h | h) <;> [left; right] <;> omega

  exact ⟨n, ⟨RelIso.mk e (fun {a b} => e_adj a b)⟩⟩
