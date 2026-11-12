import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.Op223NonsustainableTreeFinFour
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.G

/-!
# op223_local_principal_maxima_not_sufficient

Topic: graphs   Node: 5578192e8555

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; counterexample to an auxiliary eigenvector criterion

There is a tree on exactly three vertices with an edge uv that can be replaced by a nonedge so that the result remains a tree and has adjacency spectral radius at least as large, and a positive eigenvector of its adjacency matrix such that u and v each uniquely maximize that eigenvector within their respective components after deleting the edge.
-/

open SimpleGraph
open scoped Classical

open SimpleGraph Matrix
open scoped Classical

/-- The three-vertex star with centre 0 and leaves 1, 2. -/
def op223_lpm_T : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2)}

/-- The star `op223_lpm_T` with edge 01 replaced by the non-edge 12 (path 0-2-1). -/
def op223_lpm_T' : SimpleGraph (Fin 3) :=
  op223_lpm_T.deleteEdges {s(0, 1)} ⊔ SimpleGraph.fromEdgeSet {s(1, 2)}

/-- Candidate positive eigenvector `[sqrt 2, 1, 1]`. -/
noncomputable def op223_lpm_p : Fin 3 → ℝ := fun i => if i = 0 then Real.sqrt 2 else 1

lemma op223_lpm_T_edgeSet :
    op223_lpm_T.edgeSet = (↑({s(0,1), s(0,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) := by
  ext e
  induction e using Sym2.ind with
  | h a b => fin_cases a <;> fin_cases b <;> simp [op223_lpm_T, Sym2.eq, Fin.ext_iff]

lemma op223_lpm_T'_edgeSet :
    op223_lpm_T'.edgeSet = (↑({s(0,2), s(1,2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      SimpleGraph.mem_edgeSet, op223_lpm_T', op223_lpm_T, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj]
    fin_cases a <;> fin_cases b <;> simp [Sym2.eq, Fin.ext_iff]

lemma op223_lpm_T_isTree : op223_lpm_T.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    intro x; fin_cases x
    · exact SimpleGraph.Reachable.rfl
    · exact (by simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff] :
        op223_lpm_T.Adj 0 1).reachable
    · exact (by simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff] :
        op223_lpm_T.Adj 0 2).reachable
  · rw [op223_lpm_T_edgeSet, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    norm_num [Sym2.eq, Fin.ext_iff]

lemma op223_lpm_T'_isTree : op223_lpm_T'.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    intro x; fin_cases x
    · exact SimpleGraph.Reachable.rfl
    · exact (by simp [op223_lpm_T', op223_lpm_T, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
        Sym2.eq, Fin.ext_iff] : op223_lpm_T'.Adj 0 2).reachable.trans
        (by simp [op223_lpm_T', op223_lpm_T, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
        Sym2.eq, Fin.ext_iff] : op223_lpm_T'.Adj 2 1).reachable
    · exact (by simp [op223_lpm_T', op223_lpm_T, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
        Sym2.eq, Fin.ext_iff] : op223_lpm_T'.Adj 0 2).reachable
  · rw [op223_lpm_T'_edgeSet, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    norm_num [Sym2.eq, Fin.ext_iff]

/-- Reindexing a real square matrix by a permutation preserves the spectral radius. -/
lemma op223_lpm_spectral_reindex {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] (M : Matrix n n ℝ) (e : n ≃ m) :
    spectralRadius ℝ ((Matrix.reindex e e) M) = spectralRadius ℝ M := by
  have h := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ e) M
  rw [Matrix.reindexAlgEquiv_apply] at h
  simp only [spectralRadius]
  rw [h]

/-- The star and the three-vertex path are isomorphic (swap 0 and 2). -/
noncomputable def op223_lpm_iso : op223_lpm_T ≃g op223_lpm_T' :=
  RelIso.mk (Equiv.swap 0 2) (by
    intro a b
    fin_cases a <;> fin_cases b <;>
    simp only [op223_lpm_T', op223_lpm_T, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
      SimpleGraph.fromEdgeSet_adj, Equiv.swap_apply_def]
    all_goals simp [Sym2.eq, Fin.ext_iff])

/-- The star and the path have the same adjacency spectral radius. -/
lemma op223_lpm_radius_eq :
    adjacency_spectral_radius op223_lpm_T = adjacency_spectral_radius op223_lpm_T' := by
  have hmat := Iso.reindex_adjMatrix (α := ℝ) op223_lpm_iso
  have key : spectralRadius ℝ (op223_lpm_T'.adjMatrix ℝ)
      = spectralRadius ℝ (op223_lpm_T.adjMatrix ℝ) := by
    rw [← hmat]
    exact op223_lpm_spectral_reindex (op223_lpm_T.adjMatrix ℝ) (op223_lpm_iso : Fin 3 ≃ Fin 3)
  simp only [adjacency_spectral_radius]
  exact key.symm

lemma op223_lpm_p_pos (x : Fin 3) : 0 < op223_lpm_p x := by
  fin_cases x
  · simp only [op223_lpm_p, Fin.isValue, Fin.reduceEq, if_true]
    exact Real.sqrt_pos.2 (by norm_num)
  · simp [op223_lpm_p]
  · simp [op223_lpm_p]

lemma op223_lpm_p_eigen :
    (op223_lpm_T.adjMatrix ℝ).mulVec op223_lpm_p = Real.sqrt 2 • op223_lpm_p := by
  have hp0 : op223_lpm_p 0 = Real.sqrt 2 := by simp [op223_lpm_p]
  have hp1 : op223_lpm_p 1 = 1 := by simp [op223_lpm_p]
  have hp2 : op223_lpm_p 2 = 1 := by simp [op223_lpm_p]
  have h0 : op223_lpm_T.neighborFinset 0 = {1, 2} := by
    ext w; rw [SimpleGraph.mem_neighborFinset]; fin_cases w <;>
      simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]
  have h1 : op223_lpm_T.neighborFinset 1 = {0} := by
    ext w; rw [SimpleGraph.mem_neighborFinset]; fin_cases w <;>
      simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]
  have h2 : op223_lpm_T.neighborFinset 2 = {0} := by
    ext w; rw [SimpleGraph.mem_neighborFinset]; fin_cases w <;>
      simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]
  funext i
  fin_cases i
  · show (op223_lpm_T.adjMatrix ℝ *ᵥ op223_lpm_p) 0 = Real.sqrt 2 • op223_lpm_p 0
    rw [SimpleGraph.adjMatrix_mulVec_apply, h0, Finset.sum_pair (by decide), hp1, hp2, hp0,
      smul_eq_mul]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  · show (op223_lpm_T.adjMatrix ℝ *ᵥ op223_lpm_p) 1 = Real.sqrt 2 • op223_lpm_p 1
    rw [SimpleGraph.adjMatrix_mulVec_apply, h1, Finset.sum_singleton, hp0, hp1, smul_eq_mul]
    ring
  · show (op223_lpm_T.adjMatrix ℝ *ᵥ op223_lpm_p) 2 = Real.sqrt 2 • op223_lpm_p 2
    rw [SimpleGraph.adjMatrix_mulVec_apply, h2, Finset.sum_singleton, hp0, hp2, smul_eq_mul]
    ring

lemma op223_lpm_del_adj_right {a b : Fin 3} (h : (op223_lpm_T.deleteEdges {s(0,1)}).Adj a b) :
    b = 0 ∨ b = 2 := by
  fin_cases a <;> fin_cases b <;>
    simp_all [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]

lemma op223_lpm_del_adj_left {a b : Fin 3} (h : (op223_lpm_T.deleteEdges {s(0,1)}).Adj a b) :
    a = 0 ∨ a = 2 := by
  fin_cases a <;> fin_cases b <;>
    simp_all [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]

lemma op223_lpm_del_not_adj_one (b : Fin 3) : ¬ (op223_lpm_T.deleteEdges {s(0,1)}).Adj 1 b := by
  intro h
  rcases op223_lpm_del_adj_left h with h0 | h2
  · exact absurd h0 (by decide)
  · exact absurd h2 (by decide)

lemma op223_lpm_del_reach_zero (x : Fin 3)
    (h : (op223_lpm_T.deleteEdges {s(0,1)}).Reachable 0 x) : x = 0 ∨ x = 2 := by
  obtain ⟨w⟩ := h
  refine w.rec (motive := fun a b _ => (a = 0 ∨ a = 2) → (b = 0 ∨ b = 2)) ?_ ?_ (Or.inl rfl)
  · intro u hu; exact hu
  · intro u v w' hadj p ih hu
    exact ih (op223_lpm_del_adj_right hadj)

lemma op223_lpm_del_reach_one (x : Fin 3)
    (h : (op223_lpm_T.deleteEdges {s(0,1)}).Reachable 1 x) : x = 1 := by
  obtain ⟨w⟩ := h
  refine w.rec (motive := fun a b _ => a = 1 → b = 1) ?_ ?_ rfl
  · intro u hu; exact hu
  · intro u v w' hadj p ih hu
    subst hu
    exact absurd hadj (op223_lpm_del_not_adj_one v)

theorem op223_local_principal_maxima_not_sufficient : ∃ (T : SimpleGraph (Fin 3)) (u v : Fin 3) (r : ℝ) (p : Fin 3 → ℝ), T.IsTree ∧ T.Adj u v ∧ is_sustainable_edge T s(u,v) ∧ (∀ x, 0 < p x) ∧ (T.adjMatrix ℝ).mulVec p = r • p ∧ (∀ x, (T.deleteEdges {s(u,v)}).Reachable u x → x ≠ u → p x < p u) ∧ (∀ x, (T.deleteEdges {s(u,v)}).Reachable v x → x ≠ v → p x < p v) := by
  have hedge : (s(0,1) : Sym2 (Fin 3)) ∈ op223_lpm_T.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]
  have hf : (s(1,2) : Sym2 (Fin 3)) ∈ op223_lpm_Tᶜ.edgeSet := by
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
    exact ⟨by decide, by simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]⟩
  refine ⟨op223_lpm_T, 0, 1, Real.sqrt 2, op223_lpm_p, op223_lpm_T_isTree, ?_,
    ⟨hedge, s(1,2), hf, op223_lpm_T'_isTree, ?_⟩, op223_lpm_p_pos, op223_lpm_p_eigen, ?_, ?_⟩
  · simp [op223_lpm_T, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]
  · change adjacency_spectral_radius op223_lpm_T ≤ adjacency_spectral_radius op223_lpm_T'
    exact le_of_eq op223_lpm_radius_eq
  · intro x hx hxne
    rcases op223_lpm_del_reach_zero x hx with h | h
    · exact absurd h hxne
    · subst h
      have h2 : op223_lpm_p 2 = 1 := by simp [op223_lpm_p]
      have h0 : op223_lpm_p 0 = Real.sqrt 2 := by simp [op223_lpm_p]
      rw [h2, h0]
      exact Real.one_lt_sqrt_two
  · intro x hx hxne
    exact absurd (op223_lpm_del_reach_one x hx) hxne
