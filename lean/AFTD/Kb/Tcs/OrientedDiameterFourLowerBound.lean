import AFTD.Prelude
import AFTD.Kb.Tcs.OrientedDiameterBoundHolds
import AFTD.Kb.Tcs.DigraphReachWithin
import AFTD.Kb.Tcs.HasStrongOrientationOfDiameterLe
import AFTD.Kb.Tcs.IsGraphOrientation
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# oriented_diameter_four_lower_bound

Topic: graphs   Node: d5eb6fc7fe1c

Provenance: formalization of a published result. Source: arXiv:2610.09648 (An asymptotically tight bound on oriented diameter), Section 1: the general lower bound f(d) >= ceil(d^2/2) + d (from a 1978 construction, cited there), at d = 4.

f(4) >= 12: there is a finite connected bridgeless simple graph of diameter 4 that has no strong orientation of directed diameter at most 11.
-/

def ct_edges : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(5,6),(6,7),(7,8),(8,0),(1,9),(1,10),(9,10),
   (4,11),(4,12),(11,12),(5,13),(5,14),(13,14),(8,15),(8,16),(15,16)]

def ct_graph : SimpleGraph (Fin 17) :=
  SimpleGraph.fromRel (fun a b => (a.val, b.val) ∈ ct_edges)

instance ct_graph_dec : DecidableRel ct_graph.Adj := fun a b =>
  decidable_of_iff (a ≠ b ∧ ((a.val, b.val) ∈ ct_edges ∨ (b.val, a.val) ∈ ct_edges))
    (by simp [ct_graph])

def ct_pot (l : List ℕ) (i : Fin 17) : ℕ := l.getD i.val 0

theorem ct_reach_potential {V : Type*} (D : Digraph V) (φ : V → ℕ)
    (h : ∀ x y, D.Adj x y → φ y ≤ φ x + 1) :
    ∀ k u v, digraph_reach_within D k u v → φ v ≤ φ u + k
  | 0, u, v, h0 => by
      have : u = v := h0
      subst this; omega
  | k + 1, u, v, h1 => by
      rcases h1 with h1 | ⟨w, hw, h1⟩
      · have := ct_reach_potential D φ h k u v h1; omega
      · have := ct_reach_potential D φ h k w v h1
        have := h u w hw; omega

theorem ct_contra (D : Digraph (Fin 17)) (hD : is_graph_orientation ct_graph D)
    (hall : ∀ u v, digraph_reach_within D 11 u v) (l : List ℕ)
    (bad : List (Fin 17 × Fin 17)) (hbad : ∀ p ∈ bad, ¬ D.Adj p.1 p.2)
    (hG : ∀ x y, ct_graph.Adj x y → ct_pot l y ≤ ct_pot l x + 1 ∨ (x, y) ∈ bad)
    (u v : Fin 17) (huv : ct_pot l u + 11 < ct_pot l v) : False := by
  have hφ : ∀ x y, D.Adj x y → ct_pot l y ≤ ct_pot l x + 1 := by
    intro x y hxy
    rcases hG x y ((hD.1 x y).mp (Or.inl hxy)) with h | h
    · exact h
    · exact absurd hxy (hbad _ h)
  have := ct_reach_potential D (ct_pot l) hφ 11 u v (hall u v)
  omega

theorem ct_anti {D : Digraph (Fin 17)} (hD : is_graph_orientation ct_graph D) {x y : Fin 17}
    (h : D.Adj x y) : ¬ D.Adj y x := fun h' => hD.2 x y ⟨h, h'⟩

theorem ct_no_orientation_le_eleven : ¬ has_strong_orientation_of_diameter_le ct_graph 11 := by
  rintro ⟨D, hD, hall⟩
  -- region facts
  have F1 : D.Adj 0 1 ∨ D.Adj 0 4 := by
    by_contra h; push Not at h
    exact ct_contra D hD hall [0,100,100,100,100,0,0,0,0,100,100,100,100,0,0,0,0]
      [(0,1),(0,4)] (by simpa using h) (by decide +kernel) 0 2 (by decide +kernel)
  have F3 : D.Adj 5 0 ∨ D.Adj 8 0 := by
    by_contra h; push Not at h
    exact ct_contra D hD hall [100,100,100,100,100,0,0,0,0,100,100,100,100,0,0,0,0]
      [(5,0),(8,0)] (by simpa using h) (by decide +kernel) 6 0 (by decide +kernel)
  have T1 : D.Adj 1 9 ∨ D.Adj 1 10 := by
    by_contra h; push Not at h
    exact ct_contra D hD hall [0,0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0]
      [(1,9),(1,10)] (by simpa using h) (by decide +kernel) 0 9 (by decide +kernel)
  have T4 : D.Adj 4 11 ∨ D.Adj 4 12 := by
    by_contra h; push Not at h
    exact ct_contra D hD hall [0,0,0,0,0,0,0,0,0,0,0,100,100,0,0,0,0]
      [(4,11),(4,12)] (by simpa using h) (by decide +kernel) 0 11 (by decide +kernel)
  have T5 : D.Adj 13 5 ∨ D.Adj 14 5 := by
    by_contra h; push Not at h
    exact ct_contra D hD hall [100,100,100,100,100,100,100,100,100,100,100,100,100,0,0,100,100]
      [(13,5),(14,5)] (by simpa using h) (by decide +kernel) 13 0 (by decide +kernel)
  have T8 : D.Adj 15 8 ∨ D.Adj 16 8 := by
    by_contra h; push Not at h
    exact ct_contra D hD hall [100,100,100,100,100,100,100,100,100,100,100,100,100,100,100,0,0]
      [(15,8),(16,8)] (by simpa using h) (by decide +kernel) 15 0 (by decide +kernel)
  -- main potentials
  -- vertex order: 0 r; 1..4 C5#1; 5..8 C5#2; 9 10 at 1; 11 12 at 4; 13 14 at 5; 15 16 at 8
  rcases F1 with h01 | h04
  · -- s1 = 1, C5#1 long way 1,2,3,4 ; triangle at 4 gets 6
    rcases T1 with ht | ht
    · -- t1 = 9 (0), 10 (1)
      rcases F3 with h50 | h80
      · -- s2 = 5 (10), s2' = 8 (7): 8:7, 7:8, 6:9, 5:10; triangle at 8: 8,8
        rcases T5 with hs | hs
        · -- t2 = 13 (12), 14 (11)
          exact ct_contra D hD hall [6,2,3,4,5,10,9,8,7,0,1,6,6,12,11,8,8]
            [(1,0),(9,1),(0,5),(5,13)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 9 13 (by decide +kernel)
        · exact ct_contra D hD hall [6,2,3,4,5,10,9,8,7,0,1,6,6,11,12,8,8]
            [(1,0),(9,1),(0,5),(5,14)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 9 14 (by decide +kernel)
      · rcases T8 with hs | hs
        · exact ct_contra D hD hall [6,2,3,4,5,7,8,9,10,0,1,6,6,8,8,12,11]
            [(1,0),(9,1),(0,8),(8,15)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 9 15 (by decide +kernel)
        · exact ct_contra D hD hall [6,2,3,4,5,7,8,9,10,0,1,6,6,8,8,11,12]
            [(1,0),(9,1),(0,8),(8,16)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 9 16 (by decide +kernel)
    · rcases F3 with h50 | h80
      · rcases T5 with hs | hs
        · exact ct_contra D hD hall [6,2,3,4,5,10,9,8,7,1,0,6,6,12,11,8,8]
            [(1,0),(10,1),(0,5),(5,13)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 10 13 (by decide +kernel)
        · exact ct_contra D hD hall [6,2,3,4,5,10,9,8,7,1,0,6,6,11,12,8,8]
            [(1,0),(10,1),(0,5),(5,14)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 10 14 (by decide +kernel)
      · rcases T8 with hs | hs
        · exact ct_contra D hD hall [6,2,3,4,5,7,8,9,10,1,0,6,6,8,8,12,11]
            [(1,0),(10,1),(0,8),(8,15)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 10 15 (by decide +kernel)
        · exact ct_contra D hD hall [6,2,3,4,5,7,8,9,10,1,0,6,6,8,8,11,12]
            [(1,0),(10,1),(0,8),(8,16)] (by simp [ct_anti hD h01, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 10 16 (by decide +kernel)
  · -- s1 = 4: 4:2, 3:3, 2:4, 1:5; triangle at 1 gets 6; t1 in {11,12}
    rcases T4 with ht | ht
    · rcases F3 with h50 | h80
      · rcases T5 with hs | hs
        · exact ct_contra D hD hall [6,5,4,3,2,10,9,8,7,6,6,0,1,12,11,8,8]
            [(4,0),(11,4),(0,5),(5,13)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 11 13 (by decide +kernel)
        · exact ct_contra D hD hall [6,5,4,3,2,10,9,8,7,6,6,0,1,11,12,8,8]
            [(4,0),(11,4),(0,5),(5,14)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 11 14 (by decide +kernel)
      · rcases T8 with hs | hs
        · exact ct_contra D hD hall [6,5,4,3,2,7,8,9,10,6,6,0,1,8,8,12,11]
            [(4,0),(11,4),(0,8),(8,15)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 11 15 (by decide +kernel)
        · exact ct_contra D hD hall [6,5,4,3,2,7,8,9,10,6,6,0,1,8,8,11,12]
            [(4,0),(11,4),(0,8),(8,16)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 11 16 (by decide +kernel)
    · rcases F3 with h50 | h80
      · rcases T5 with hs | hs
        · exact ct_contra D hD hall [6,5,4,3,2,10,9,8,7,6,6,1,0,12,11,8,8]
            [(4,0),(12,4),(0,5),(5,13)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 12 13 (by decide +kernel)
        · exact ct_contra D hD hall [6,5,4,3,2,10,9,8,7,6,6,1,0,11,12,8,8]
            [(4,0),(12,4),(0,5),(5,14)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h50, ct_anti hD hs]) (by decide +kernel) 12 14 (by decide +kernel)
      · rcases T8 with hs | hs
        · exact ct_contra D hD hall [6,5,4,3,2,7,8,9,10,6,6,1,0,8,8,12,11]
            [(4,0),(12,4),(0,8),(8,15)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 12 15 (by decide +kernel)
        · exact ct_contra D hD hall [6,5,4,3,2,7,8,9,10,6,6,1,0,8,8,11,12]
            [(4,0),(12,4),(0,8),(8,16)] (by simp [ct_anti hD h04, ct_anti hD ht, ct_anti hD h80, ct_anti hD hs]) (by decide +kernel) 12 16 (by decide +kernel)

def ct_bfs (H : SimpleGraph (Fin 17)) [DecidableRel H.Adj] : ℕ → Fin 17 → Finset (Fin 17)
  | 0, u => {u}
  | k + 1, u => ct_bfs H k u ∪ Finset.univ.filter (fun y => ∃ x ∈ ct_bfs H k u, H.Adj x y)

theorem ct_bfs_walk (H : SimpleGraph (Fin 17)) [DecidableRel H.Adj] :
    ∀ k u y, y ∈ ct_bfs H k u → ∃ p : H.Walk u y, p.length ≤ k
  | 0, u, y, h => by
      simp [ct_bfs] at h; subst h; exact ⟨SimpleGraph.Walk.nil, le_refl _⟩
  | k + 1, u, y, h => by
      simp only [ct_bfs, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h
      rcases h with h | ⟨x, hx, hxy⟩
      · obtain ⟨p, hp⟩ := ct_bfs_walk H k u y h; exact ⟨p, by omega⟩
      · obtain ⟨p, hp⟩ := ct_bfs_walk H k u x hx
        exact ⟨p.concat hxy, by rw [SimpleGraph.Walk.length_concat]; omega⟩

theorem ct_walk_potential (φ : Fin 17 → ℕ) (h : ∀ x y, ct_graph.Adj x y → φ y ≤ φ x + 1) :
    ∀ {u v : Fin 17} (p : ct_graph.Walk u v), φ v ≤ φ u + p.length
  | _, _, .nil => by simp
  | _, _, .cons hxy p => by
      have := ct_walk_potential φ h p
      have := h _ _ hxy
      simp only [SimpleGraph.Walk.length_cons]; omega

theorem ct_to_root : ∀ u : Fin 17, (0 : Fin 17) ∈ ct_bfs ct_graph 2 u := by decide +kernel

theorem ct_edist_root (u : Fin 17) : ct_graph.edist u 0 ≤ 2 := by
  obtain ⟨p, hp⟩ := ct_bfs_walk ct_graph 2 u 0 (ct_to_root u)
  exact (SimpleGraph.edist_le p).trans (by exact_mod_cast hp)

theorem ct_connected : ct_graph.Connected := by
  have h : ∀ u, ct_graph.Reachable u 0 := fun u =>
    (ct_bfs_walk ct_graph 2 u 0 (ct_to_root u)).elim fun p _ => ⟨p⟩
  exact ⟨fun u v => (h u).trans (h v).symm⟩

theorem ct_ediam : ct_graph.ediam = 4 := by
  apply le_antisymm
  · apply SimpleGraph.ediam_le_of_edist_le
    intro u v
    calc ct_graph.edist u v ≤ ct_graph.edist u 0 + ct_graph.edist 0 v := SimpleGraph.edist_triangle
      _ ≤ 2 + 2 := by
          gcongr
          · exact ct_edist_root u
          · rw [SimpleGraph.edist_comm]; exact ct_edist_root v
      _ = 4 := by norm_num
  · obtain ⟨p, hp⟩ := (ct_connected 9 13).exists_walk_length_eq_edist
    have := ct_walk_potential (ct_pot [2,1,2,3,3,3,4,4,3,0,1,4,4,4,4,4,4]) (by decide +kernel) p
    have h4 : 4 ≤ p.length := by simpa [ct_pot] using this
    calc (4 : ℕ∞) ≤ p.length := by exact_mod_cast h4
      _ = ct_graph.edist 9 13 := hp
      _ ≤ ct_graph.ediam := SimpleGraph.edist_le_ediam

theorem ct_diam : ct_graph.diam = 4 := by
  rw [SimpleGraph.diam, ct_ediam]; rfl

@[instance_reducible] def ct_del_dec (x y : Fin 17) : DecidableRel (ct_graph.deleteEdges {s(x, y)}).Adj := fun a b =>
  decidable_of_iff (ct_graph.Adj a b ∧ ¬((a = x ∧ b = y) ∨ (a = y ∧ b = x)))
    (by simp [SimpleGraph.deleteEdges_adj])

theorem ct_cycles : ∀ x y : Fin 17, ct_graph.Adj x y →
    y ∈ @ct_bfs (ct_graph.deleteEdges {s(x, y)}) (ct_del_dec x y) 4 x := by decide +kernel

theorem ct_bridgeless : ∀ e, ¬ ct_graph.IsBridge e := by
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.isBridge_iff, not_not]
    by_cases h : ct_graph.Adj x y
    · obtain ⟨p, _⟩ := @ct_bfs_walk _ (ct_del_dec x y) 4 x y (ct_cycles x y h)
      exact ⟨p⟩
    · have hle : ct_graph ≤ ct_graph.deleteEdges {s(x, y)} := by
        intro a b hab
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hab, ?_⟩
        intro hm
        simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h hab
        · exact h hab.symm
      exact (ct_connected x y).mono hle

theorem oriented_diameter_four_lower_bound : ¬ oriented_diameter_bound_holds 4 11 := fun h =>
  ct_no_orientation_le_eleven (h 17 ct_graph ct_connected ct_bridgeless ct_diam)
