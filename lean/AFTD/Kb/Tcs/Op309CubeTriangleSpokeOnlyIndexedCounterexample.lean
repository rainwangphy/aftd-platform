import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IndexedEdgeAdj
import AFTD.Kb.Tcs.Op309IndexedEdgeRich
import AFTD.Kb.Tcs.Op309IndexedRichNeighbor

/-!
# op309_cube_triangle_spoke_only_indexed_counterexample

Topic: graphs   Node: 0b3bedf98a79

Provenance: helper lemma. OP-309 triangle contraction fixed-color obstruction

For the two explicitly listed indexed-edge graphs, the first displayed coloring is rich-neighbor; no coloring obtained by changing only the three spokes and three new triangle edges is rich-neighbor; and the displayed coloring changing one further old edge is rich-neighbor.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
local instance {n m : ℕ} (E : Fin n → Fin m × Fin m) (i j : Fin n) : Decidable (op309_indexed_edge_adj E i j) := by
  unfold op309_indexed_edge_adj
  infer_instance

local instance {n m : ℕ} (E : Fin n → Fin m × Fin m) (C : Fin n → Fin 5) (i : Fin n) : Decidable (op309_indexed_edge_rich E C i) := by
  unfold op309_indexed_edge_rich
  infer_instance

local instance {n m : ℕ} (E : Fin n → Fin m × Fin m) (C : Fin n → Fin 5) : Decidable (op309_indexed_rich_neighbor E C) := by
  unfold op309_indexed_rich_neighbor
  infer_instance


private theorem in1115_recolor_core
    (s0 s1 s2 a b c : Fin 5)
    (hs23 : s2 ≠ 3) (hs24 : s2 ≠ 4) (hsc : s2 ≠ c)
    (h3 : ([1,s0,3,0] : List (Fin 5)).Nodup ∨ ([3,4,a,c] : List (Fin 5)).Nodup)
    (h7 : ([3,4,b,c] : List (Fin 5)).Nodup)
    (h9 : ([s0,s2,a,c] : List (Fin 5)).Nodup ∨ ([s1,s2,a,b] : List (Fin 5)).Nodup)
    (h11 : ([2,s0,4,3] : List (Fin 5)).Nodup) : False := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.nodup_singleton, not_or, ne_eq] at *
  omega

private theorem in1115_local_rich_four {n m : ℕ}
    (E : Fin n → Fin m × Fin m) (C : Fin n → Fin 5) (e i j k l : Fin n)
    (hr : op309_indexed_edge_rich E C e) (hd : ([i,j,k,l] : List (Fin n)).Nodup)
    (hn : ∀ x ∈ ([i,j,k,l] : List (Fin n)), op309_indexed_edge_adj E e x) :
    ([C i,C j,C k,C l] : List (Fin 5)).Nodup := by
  have hi := hn i (by simp)
  have hj := hn j (by simp)
  have hk := hn k (by simp)
  have hl := hn l (by simp)
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.nodup_singleton,not_or] at hd ⊢
  dsimp [op309_indexed_edge_rich] at hr
  aesop

private def in1115_F : Fin 15 → Fin 10 × Fin 10 :=
 ![(0,1),(0,6),(0,7),(1,2),(1,5),(2,4),(2,8),(3,4),(3,6),(3,9),(4,5),(5,6),(7,8),(7,9),(8,9)]

private def in1115_C (s0 s1 s2 a b c : Fin 5) : Fin 15 → Fin 5 :=
 ![2,1,s0,3,0,4,s1,3,4,s2,2,3,a,b,c]

private theorem in1115_spoke_only_no_extension (s0 s1 s2 a b c : Fin 5) :
    ¬ op309_indexed_rich_neighbor in1115_F (in1115_C s0 s1 s2 a b c) := by
  intro hv
  have hs23 : s2 ≠ 3 := by
    have hh := hv.1 9 7 (by decide)
    simpa [in1115_C] using hh
  have hs24 : s2 ≠ 4 := by
    have hh := hv.1 9 8 (by decide)
    simpa [in1115_C] using hh
  have hsc : s2 ≠ c := by
    have hh := hv.1 9 14 (by decide)
    simpa [in1115_C] using hh
  have h3 : ([1,s0,3,0] : List (Fin 5)).Nodup ∨ ([3,4,a,c] : List (Fin 5)).Nodup := by
    obtain ⟨j,hj,hr⟩ := hv.2 3 (by exact ⟨0,by decide⟩)
    have hc : j=0 ∨ j=4 ∨ j=5 ∨ j=6 := by
      fin_cases j <;> simp_all [op309_indexed_edge_adj,in1115_F]
    rcases hc with rfl|rfl|rfl|rfl
    · left
      have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 0 1 2 3 4 hr (by decide) (by decide)
      simpa [in1115_C] using hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 4 0 3 10 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 5 3 6 7 10 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · right
      have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 6 3 5 12 14 hr (by decide) (by decide)
      simpa [in1115_C] using hh
  have h7 : ([3,4,b,c] : List (Fin 5)).Nodup := by
    obtain ⟨j,hj,hr⟩ := hv.2 7 (by exact ⟨5,by decide⟩)
    have hc : j=5 ∨ j=8 ∨ j=9 ∨ j=10 := by
      fin_cases j <;> simp_all [op309_indexed_edge_adj,in1115_F]
    rcases hc with rfl|rfl|rfl|rfl
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 5 3 6 7 10 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 8 1 7 9 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 9 7 8 13 14 hr (by decide) (by decide)
      simpa [in1115_C] using hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 10 4 5 7 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
  have h9 : ([s0,s2,a,c] : List (Fin 5)).Nodup ∨ ([s1,s2,a,b] : List (Fin 5)).Nodup := by
    obtain ⟨j,hj,hr⟩ := hv.2 9 (by exact ⟨7,by decide⟩)
    have hc : j=7 ∨ j=8 ∨ j=13 ∨ j=14 := by
      fin_cases j <;> simp_all [op309_indexed_edge_adj,in1115_F]
    rcases hc with rfl|rfl|rfl|rfl
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 7 5 8 9 10 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 8 1 7 9 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · left
      have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 13 2 9 12 14 hr (by decide) (by decide)
      simpa [in1115_C] using hh
    · right
      have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 14 6 9 12 13 hr (by decide) (by decide)
      simpa [in1115_C] using hh
  have h11 : ([2,s0,4,3] : List (Fin 5)).Nodup := by
    obtain ⟨j,hj,hr⟩ := hv.2 11 (by exact ⟨1,by decide⟩)
    have hc : j=1 ∨ j=4 ∨ j=8 ∨ j=10 := by
      fin_cases j <;> simp_all [op309_indexed_edge_adj,in1115_F]
    rcases hc with rfl|rfl|rfl|rfl
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 1 0 2 8 11 hr (by decide) (by decide)
      simpa [in1115_C] using hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 4 0 3 10 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 8 1 7 9 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
    · have hh := in1115_local_rich_four in1115_F (in1115_C s0 s1 s2 a b c) 10 4 5 7 11 hr (by decide) (by decide)
      simp [in1115_C] at hh
  exact in1115_recolor_core s0 s1 s2 a b c hs23 hs24 hsc h3 h7 h9 h11

private def in1115_E0 : Fin 12 → Fin 8 × Fin 8 :=
 ![(0,1),(0,3),(0,4),(1,2),(1,7),(2,3),(2,6),(3,5),(4,5),(4,7),(5,6),(6,7)]
private def in1115_D0 : Fin 12 → Fin 5 := ![0,1,2,2,1,3,0,4,3,4,2,3]
private def in1115_repaired : Fin 15 → Fin 5 := ![2,1,0,1,0,4,0,3,4,1,2,3,2,4,3]

theorem op309_cube_triangle_spoke_only_indexed_counterexample :
  let E0 : Fin 12 → Fin 8 × Fin 8 :=
    ![(0,1),(0,3),(0,4),(1,2),(1,7),(2,3),(2,6),(3,5),(4,5),(4,7),(5,6),(6,7)]
  let E1 : Fin 15 → Fin 10 × Fin 10 :=
    ![(0,1),(0,6),(0,7),(1,2),(1,5),(2,4),(2,8),(3,4),(3,6),(3,9),(4,5),(5,6),(7,8),(7,9),(8,9)]
  let C0 : Fin 12 → Fin 5 := ![0,1,2,2,1,3,0,4,3,4,2,3]
  let C1 : Fin 15 → Fin 5 := ![2,1,0,1,0,4,0,3,4,1,2,3,2,4,3]
  op309_indexed_rich_neighbor E0 C0 ∧
    (∀ s0 s1 s2 a b c : Fin 5,
      ¬ op309_indexed_rich_neighbor E1 ![2,1,s0,3,0,4,s1,3,4,s2,2,3,a,b,c]) ∧
    op309_indexed_rich_neighbor E1 C1 := by
  dsimp only
  exact ⟨by decide,in1115_spoke_only_no_extension,by decide⟩
