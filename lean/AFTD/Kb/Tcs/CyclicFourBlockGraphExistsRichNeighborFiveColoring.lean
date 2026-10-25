import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicFourBlockGraph
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphRichNeighborColoringOfEdgeFamily
import AFTD.Kb.Tcs.CyclicFourBlockTouchIff
import AFTD.Kb.Tcs.CyclicFourBlockNondiag
import AFTD.Kb.Tcs.CyclicFourBlockSrc
import AFTD.Kb.Tcs.CyclicFourBlockColNat
import AFTD.Kb.Tcs.CyclicFourBlockTouch
import AFTD.Kb.Tcs.CyclicFourBlockW
import AFTD.Kb.Tcs.CyclicFourBlockGood
import AFTD.Kb.Tcs.CyclicFourBlockPrev
import AFTD.Kb.Tcs.CyclicFourBlockDst
import AFTD.Kb.Tcs.CyclicFourBlockCol
import AFTD.Kb.Tcs.CyclicFourBlockWitness
import AFTD.Kb.Tcs.CyclicFourBlockN
import AFTD.Kb.Tcs.CyclicFourBlockProper
import AFTD.Kb.Tcs.CyclicFourBlockNext
import AFTD.Kb.Tcs.CyclicFourBlockEdge

/-!
# cyclic_four_block_graph_exists_rich_neighbor_five_coloring

Topic: graphs   Node: c4a302b45f9c

Provenance: helper lemma. Explicit helper partial case for OP-309 (arXiv:2610.21868, Conjecture 1.1). The underlying standard cyclic cubic family has known related normal five-colorings (arXiv:2306.13340); the proposed proof uses the concrete palette found here in experiment4686. No novelty or research-level claim is made.

For every m>=0, cyclic_four_block_graph m, on 4(2m+5) vertices, admits a rich-neighbor five-edge-coloring.
-/

set_option maxHeartbeats 4000000 in
/-- The witness edge `cyclic_four_block_W m e` always has small role index. -/
theorem cyclic_four_block_graph_exists_rich_neighbor_five_coloring_W_role (m : ℕ)
    (e : Fin (2*m+5) × Fin 6) : (cyclic_four_block_W m e).2.val ≤ 3 := by
  obtain ⟨i,j⟩ := e
  fin_cases j <;>
    (simp only [cyclic_four_block_W, Fin.reduceFinMk, Matrix.cons_val] <;>
     (try split_ifs) <;>
     first | decide | simp)

set_option maxHeartbeats 4000000 in
/-- Every edge touching an indexed edge of role at most three is one of the four indexed edges
listed by `cyclic_four_block_N`. -/
theorem cyclic_four_block_graph_exists_rich_neighbor_five_coloring_cover (m : ℕ)
    (e f : Fin (2*m+5) × Fin 6) (hj : e.2.val ≤ 3)
    (hne : cyclic_four_block_edge m e ≠ cyclic_four_block_edge m f) (ht : cyclic_four_block_touch m e f) :
    f = cyclic_four_block_N m e (⟨0,by decide⟩ : Fin 4) ∨
    f = cyclic_four_block_N m e (⟨1,by decide⟩ : Fin 4) ∨
    f = cyclic_four_block_N m e (⟨2,by decide⟩ : Fin 4) ∨
    f = cyclic_four_block_N m e (⟨3,by decide⟩ : Fin 4) := by
  obtain ⟨i,j⟩ := e
  obtain ⟨k,l⟩ := f
  have hne' : ¬ ((i,j) = (k,l)) := fun h => hne (by rw [h])
  fin_cases j
  · fin_cases l <;>
      simp only [cyclic_four_block_touch, cyclic_four_block_src, cyclic_four_block_dst,
        cyclic_four_block_next, cyclic_four_block_prev, cyclic_four_block_N,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
        and_true] at ht hne' ⊢ <;>
      (try split_ifs at ht hne' ⊢) <;>
      (try simp only [and_true] at ht hne' ⊢) <;>
      omega
  · fin_cases l <;>
      simp only [cyclic_four_block_touch, cyclic_four_block_src, cyclic_four_block_dst,
        cyclic_four_block_next, cyclic_four_block_prev, cyclic_four_block_N,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
        and_true] at ht hne' ⊢ <;>
      (try split_ifs at ht hne' ⊢) <;>
      (try simp only [and_true] at ht hne' ⊢) <;>
      omega
  · fin_cases l <;>
      simp only [cyclic_four_block_touch, cyclic_four_block_src, cyclic_four_block_dst,
        cyclic_four_block_next, cyclic_four_block_prev, cyclic_four_block_N,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
        and_true] at ht hne' ⊢ <;>
      (try split_ifs at ht hne' ⊢) <;>
      (try simp only [and_true] at ht hne' ⊢) <;>
      omega
  · fin_cases l <;>
      simp only [cyclic_four_block_touch, cyclic_four_block_src, cyclic_four_block_dst,
        cyclic_four_block_next, cyclic_four_block_prev, cyclic_four_block_N,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
        and_true] at ht hne' ⊢ <;>
      (try split_ifs at ht hne' ⊢) <;>
      (try simp only [and_true] at ht hne' ⊢) <;>
      omega
  · have h4 : (⟨4, by decide⟩ : Fin 6).val ≤ 3 := hj
    exact absurd h4 (by decide)
  · have h5 : (⟨5, by decide⟩ : Fin 6).val ≤ 3 := hj
    exact absurd h5 (by decide)

set_option maxHeartbeats 4000000 in
/-- The four neighbours of a good indexed edge of `cyclic_four_block_graph m` receive four
distinct colours. -/
theorem cyclic_four_block_graph_exists_rich_neighbor_five_coloring_good_injective (m : ℕ)
    (e : Fin (2*m+5) × Fin 6) (he : cyclic_four_block_good m e) :
    Function.Injective (fun k => cyclic_four_block_col m (cyclic_four_block_N m e k)) := by
  intro a b hab
  apply Fin.ext
  have hab' : cyclic_four_block_col_nat m (cyclic_four_block_N m e a)
      = cyclic_four_block_col_nat m (cyclic_four_block_N m e b) := congrArg Fin.val hab
  obtain ⟨i,j⟩ := e
  have he' : (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ ((j : ℕ) = 0 ∧ 0 < (i:ℕ) ∧ (i:ℕ) + 1 < 2*m+5) ∨
      ((j : ℕ) = 3 ∧ (i:ℕ) + 2 = 2*m+5) := he
  rcases he' with h | h | ⟨h,hi0,hin⟩ | ⟨h,hlast⟩
  · have hj : j = (⟨1, by decide⟩ : Fin 6) := Fin.ext h
    rw [hj] at hab'
    fin_cases a <;> fin_cases b <;>
      simp only [cyclic_four_block_col_nat, cyclic_four_block_N, cyclic_four_block_next,
        cyclic_four_block_prev, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue,
        Fin.val_mk] at hab' ⊢ <;>
      (try split_ifs at hab' ⊢) <;>
      (try simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.isValue, Fin.val_mk] at hab' ⊢) <;>
      omega
  · have hj : j = (⟨2, by decide⟩ : Fin 6) := Fin.ext h
    rw [hj] at hab'
    fin_cases a <;> fin_cases b <;>
      simp only [cyclic_four_block_col_nat, cyclic_four_block_N, cyclic_four_block_next,
        cyclic_four_block_prev, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue,
        Fin.val_mk] at hab' ⊢ <;>
      (try split_ifs at hab' ⊢) <;>
      (try simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.isValue, Fin.val_mk] at hab' ⊢) <;>
      omega
  · have hj : j = (⟨0, by decide⟩ : Fin 6) := Fin.ext h
    rw [hj] at hab'
    fin_cases a <;> fin_cases b <;>
      simp only [cyclic_four_block_col_nat, cyclic_four_block_N, cyclic_four_block_next,
        cyclic_four_block_prev, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue,
        Fin.val_mk] at hab' ⊢ <;>
      (try split_ifs at hab' ⊢) <;>
      (try simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.isValue, Fin.val_mk] at hab' ⊢) <;>
      omega
  · have hj : j = (⟨3, by decide⟩ : Fin 6) := Fin.ext h
    rw [hj] at hab'
    fin_cases a <;> fin_cases b <;>
      simp only [cyclic_four_block_col_nat, cyclic_four_block_N, cyclic_four_block_next,
        cyclic_four_block_prev, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue,
        Fin.val_mk] at hab' ⊢ <;>
      (try split_ifs at hab' ⊢) <;>
      (try simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.isValue, Fin.val_mk] at hab' ⊢) <;>
      omega

theorem cyclic_four_block_graph_exists_rich_neighbor_five_coloring (m : ℕ) :
    ∃ c : (cyclic_four_block_graph m).lineGraph.Coloring (Fin 5),
      simple_graph_is_rich_neighbor_coloring (cyclic_four_block_graph m) c := by
  change ∃ c : (SimpleGraph.fromEdgeSet (Set.range (cyclic_four_block_edge m))).lineGraph.Coloring (Fin 5),
    simple_graph_is_rich_neighbor_coloring (SimpleGraph.fromEdgeSet (Set.range (cyclic_four_block_edge m))) c
  apply simple_graph_rich_neighbor_coloring_of_edge_family (cyclic_four_block_edge m)
    (cyclic_four_block_nondiag m) (cyclic_four_block_col m)
  · intro i j hne ht
    exact cyclic_four_block_proper m i j hne ((cyclic_four_block_touch_iff m i j).mpr ht)
  · intro i
    obtain ⟨hne, ht, hgood⟩ := cyclic_four_block_witness m i
    have hw : (cyclic_four_block_W m i).2.val ≤ 3 :=
      cyclic_four_block_graph_exists_rich_neighbor_five_coloring_W_role m i
    refine ⟨cyclic_four_block_W m i, hne, (cyclic_four_block_touch_iff _ _ _).mp ht, ?_⟩
    intro k l hkl hjk hjl hcolor
    have hk := cyclic_four_block_graph_exists_rich_neighbor_five_coloring_cover m _ k hw hjk.1
      ((cyclic_four_block_touch_iff _ _ _).mpr hjk.2)
    have hl := cyclic_four_block_graph_exists_rich_neighbor_five_coloring_cover m _ l hw hjl.1
      ((cyclic_four_block_touch_iff _ _ _).mpr hjl.2)
    obtain ⟨a, ha⟩ : ∃ a : Fin 4, k = cyclic_four_block_N m (cyclic_four_block_W m i) a := by
      rcases hk with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin 4, l = cyclic_four_block_N m (cyclic_four_block_W m i) b := by
      rcases hl with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    have hab := cyclic_four_block_graph_exists_rich_neighbor_five_coloring_good_injective m _
      hgood (by simpa [ha, hb] using hcolor)
    exact hkl (by rw [ha, hb, hab])
