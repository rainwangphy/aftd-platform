import AFTD.Prelude
import AFTD.Kb.Tcs.IsDistanceHereditary

/-!
# tree_is_distance_hereditary

Topic: graphs   Node: beda0f5ed6e4

Provenance: formalization of a published result. Source: Howarka 1977

Every tree is distance-hereditary.
-/

/-- Every tree is distance-hereditary. -/
theorem tree_is_distance_hereditary {α : Type*} (T : SimpleGraph α) (hT : T.IsTree) :
    is_distance_hereditary T := by
  intro s u v huv
  -- A shortest walk `p` inside the induced subgraph, and the unique `T`-path `q` between `u` and `v`.
  obtain ⟨p, hppath, hplen⟩ := huv.exists_path_of_dist
  obtain ⟨q, hqpath, hqlen⟩ := hT.connected.exists_path_of_dist (u : α) (v : α)
  have hinj : Function.Injective (⇑(SimpleGraph.Embedding.induce s : T.induce s ↪g T)) :=
    fun a b h => Subtype.ext h
  have hpT : (p.map (SimpleGraph.Embedding.induce s).toHom).IsPath := hppath.map hinj
  -- Uniqueness of paths in a tree: the image of `p` in `T` is already the `T`-path from `u` to `v`.
  have hEq : p.map (SimpleGraph.Embedding.induce s).toHom = q :=
    (hT.existsUnique_path (u : α) (v : α)).unique hpT hqpath
  -- Hence every vertex of `q` lies in `s`.
  have hsupp : ∀ x ∈ q.support, x ∈ s := by
    intro x hx
    have h1 : q.support = p.support.map (fun y : s => (y : α)) := by
      rw [← hEq]
      exact SimpleGraph.Walk.support_map _ p
    rw [h1] at hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  refine le_antisymm ?_ ?_
  · -- `q` can be pushed into the induced subgraph, giving a walk there of length `T.dist u v`.
    have hlen : (q.induce s hsupp).length = q.length := by
      rw [← SimpleGraph.Walk.length_map (SimpleGraph.Embedding.induce s).toHom (q.induce s hsupp),
        SimpleGraph.Walk.map_induce]
      rfl
    have h : (T.induce s).dist ⟨(u:α), hsupp _ q.start_mem_support⟩
        ⟨(v:α), hsupp _ q.end_mem_support⟩ ≤ (q.induce s hsupp).length := SimpleGraph.dist_le _
    rw [hlen, hqlen] at h
    exact h
  · -- Conversely, `p` is a walk of `T`, so it bounds `T.dist u v`.
    calc T.dist (u : α) (v : α) ≤ (p.map (SimpleGraph.Embedding.induce s).toHom).length :=
        SimpleGraph.dist_le _
      _ = (T.induce s).dist u v := by rw [SimpleGraph.Walk.length_map, hplen]
