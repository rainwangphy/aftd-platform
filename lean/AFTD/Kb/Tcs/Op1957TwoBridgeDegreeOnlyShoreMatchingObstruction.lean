import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleTwoOddAnticompleteShoresComplementUnmatchable
import AFTD.Kb.Tcs.GraphMatchingEncardLeVertexCoverEncard

/-!
# op1957_two_bridge_degree_only_shore_matching_obstruction

Topic: graphs   Node: cbe8edae2c8f

Provenance: helper lemma. Explicit degree-only obstruction to the general two-bridge shore-matching step for OP-1957, found in experiment 35093; the graph is not claimed to satisfy the first equality witness or minimality.

An explicit 48-vertex graph H of maximum degree 21 has adjacent saturated twins 0,1, and distinct nonneighbors 2,3 that share no H-neighbor with 0. An eight-vertex set Q consists of saturated vertices with common H-neighborhood W ∪ {2,3}, where W has 19 vertices; each of two 14-vertex subsets W₁,W₂ covering W, as well as Q, induces a perfect matching in the complement G. But G[W] has matching number at most seven, and G is not 12-extendible.
-/

def op1957_shore_barrier_base (a b : Fin 48) : Prop :=
  (a.val < 2 ∧ (b.val < 2 ∨ b.val = 4 ∨ (5 ≤ b.val ∧ b.val < 24))) ∨
  ((12 ≤ a.val ∧ a.val < 24) ∧ (12 ≤ b.val ∧ b.val < 24)) ∨
  ((24 ≤ a.val ∧ a.val < 32) ∧ ((5 ≤ b.val ∧ b.val < 24) ∨ b.val = 2 ∨ b.val = 3))

def op1957_shore_barrier_H : SimpleGraph (Fin 48) where
  Adj a b := a ≠ b ∧ (op1957_shore_barrier_base a b ∨ op1957_shore_barrier_base b a)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance : DecidableRel op1957_shore_barrier_H.Adj := fun a b => by
  change Decidable (a ≠ b ∧ (op1957_shore_barrier_base a b ∨ op1957_shore_barrier_base b a))
  unfold op1957_shore_barrier_base
  infer_instance

def op1957_shore_barrier_G : SimpleGraph (Fin 48) := op1957_shore_barrier_Hᶜ
instance : DecidableRel op1957_shore_barrier_G.Adj := inferInstanceAs (DecidableRel (op1957_shore_barrier_Hᶜ).Adj)

def op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution
    {V : Type*} (G : SimpleGraph V) (f : V → V)
    (h_inv : ∀ v, f (f v) = v) (h_adj : ∀ v, G.Adj v (f v)) : G.Subgraph where
  verts := Set.univ
  Adj v w := w = f v
  adj_sub := by
    intro v w hw
    subst hw
    exact h_adj v
  edge_vert := by intro v w hw; trivial
  symm := by
    constructor
    intro v w hw
    show v = f w
    rw [hw, h_inv]

theorem op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution_isPerfectMatching
    {V : Type*} (G : SimpleGraph V) (f : V → V)
    (h_inv : ∀ v, f (f v) = v) (h_adj : ∀ v, G.Adj v (f v)) :
    (op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution G f h_inv h_adj).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  refine ⟨f v, rfl, ?_⟩
  intro w hw
  exact hw

theorem op1957_two_bridge_degree_only_shore_matching_obstruction :
    let W : Finset (Fin 48) := Finset.univ.filter (fun v => 5 ≤ v.val ∧ v.val < 24)
    let W₁ : Finset (Fin 48) := Finset.univ.filter (fun v => 5 ≤ v.val ∧ v.val < 19)
    let W₂ : Finset (Fin 48) := Finset.univ.filter (fun v => (5 ≤ v.val ∧ v.val < 12) ∨ (17 ≤ v.val ∧ v.val < 24))
    let Q : Finset (Fin 48) := Finset.univ.filter (fun v => 24 ≤ v.val ∧ v.val < 32)
    (∀ a, (op1957_shore_barrier_H.neighborFinset a).card ≤ 21) ∧
    op1957_shore_barrier_H.Adj 0 1 ∧
    (op1957_shore_barrier_H.neighborFinset 0).card = 21 ∧
    (∀ a, a ≠ 0 → a ≠ 1 → (op1957_shore_barrier_H.Adj 0 a ↔ op1957_shore_barrier_H.Adj 1 a)) ∧
    ¬ op1957_shore_barrier_H.Adj 0 2 ∧ ¬ op1957_shore_barrier_H.Adj 0 3 ∧
    (∀ a, op1957_shore_barrier_H.Adj 0 a → ¬ op1957_shore_barrier_H.Adj 2 a ∧ ¬ op1957_shore_barrier_H.Adj 3 a) ∧
    (∀ q ∈ Q, op1957_shore_barrier_H.neighborFinset q = W ∪ {2, 3}) ∧
    (∃ M : (op1957_shore_barrier_G.induce {v | v ∈ W₁}).Subgraph, M.IsPerfectMatching) ∧
    (∃ M : (op1957_shore_barrier_G.induce {v | v ∈ W₂}).Subgraph, M.IsPerfectMatching) ∧
    (∃ M : (op1957_shore_barrier_G.induce {v | v ∈ Q}).Subgraph, M.IsPerfectMatching) ∧
    (∀ M : (op1957_shore_barrier_G.induce {v | v ∈ W}).Subgraph,
       M.IsMatching → M.edgeSet.ncard ≤ 7) ∧
    ¬ is_k_extendable op1957_shore_barrier_G 12 := by
  intro W W₁ W₂ Q
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · let f₁ (v : {v : Fin 48 // v ∈ W₁}) : {v : Fin 48 // v ∈ W₁} :=
      if h : v.val.val < 12 then
        ⟨⟨v.val.val + 7, by omega⟩, by
          revert v h; decide⟩
      else
        ⟨⟨v.val.val - 7, by omega⟩, by
          revert v h; decide⟩
    have f₁_inv (v : {v : Fin 48 // v ∈ W₁}) : f₁ (f₁ v) = v := by
      revert v; decide
    have f₁_adj (v : {v : Fin 48 // v ∈ W₁}) :
        (op1957_shore_barrier_G.induce {x | x ∈ W₁}).Adj v (f₁ v) := by
      revert v; decide
    exact ⟨op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution _ f₁ f₁_inv f₁_adj,
      op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution_isPerfectMatching _ _ _ _⟩
  · let f₂ (v : {v : Fin 48 // v ∈ W₂}) : {v : Fin 48 // v ∈ W₂} :=
      if h : v.val.val < 12 then
        ⟨⟨v.val.val + 12, by omega⟩, by
          revert v h; decide⟩
      else
        ⟨⟨v.val.val - 12, by omega⟩, by
          revert v h; decide⟩
    have f₂_inv (v : {v : Fin 48 // v ∈ W₂}) : f₂ (f₂ v) = v := by
      revert v; decide
    have f₂_adj (v : {v : Fin 48 // v ∈ W₂}) :
        (op1957_shore_barrier_G.induce {x | x ∈ W₂}).Adj v (f₂ v) := by
      revert v; decide
    exact ⟨op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution _ f₂ f₂_inv f₂_adj,
      op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution_isPerfectMatching _ _ _ _⟩
  · let fQ (v : {v : Fin 48 // v ∈ Q}) : {v : Fin 48 // v ∈ Q} :=
      if h : v.val.val % 2 = 0 then
        ⟨⟨v.val.val + 1, by omega⟩, by
          revert v h; decide⟩
      else
        ⟨⟨v.val.val - 1, by omega⟩, by
          revert v h; decide⟩
    have fQ_inv (v : {v : Fin 48 // v ∈ Q}) : fQ (fQ v) = v := by
      revert v; decide
    have fQ_adj (v : {v : Fin 48 // v ∈ Q}) :
        (op1957_shore_barrier_G.induce {x | x ∈ Q}).Adj v (fQ v) := by
      revert v; decide
    exact ⟨op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution _ fQ fQ_inv fQ_adj,
      op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution_isPerfectMatching _ _ _ _⟩
  · intro M hM
    let c_W : Set {v : Fin 48 // v ∈ W} := {v | v.val.val < 12}
    have c_W_encard : c_W.encard = 7 := by
      have : c_W = (Finset.univ.filter (fun (v : {v : Fin 48 // v ∈ W}) => v.val.val < 12) : Set _) := by
        ext; simp [c_W]
      rw [this, Set.encard_coe_eq_coe_finsetCard]
      norm_num
      decide
    have c_W_cover : (op1957_shore_barrier_G.induce {v | v ∈ W}).IsVertexCover c_W := by
      intro ⟨v, hv⟩ ⟨w, hw⟩ hadj
      simp only [c_W]
      revert v w hv hw hadj
      decide
    have h := graph_matching_encard_le_vertex_cover_encard _ M c_W hM c_W_cover
    rw [c_W_encard] at h
    exact (Set.encard_le_coe_iff_finite_ncard_le.mp h).2
  · intro hExt
    let K₅ : Finset (Fin 48) := Finset.univ.filter (fun v => 24 ≤ v.val ∧ v.val < 29)
    let C : Finset (Fin 48) := Finset.univ.filter (fun v => v ∉ K₅ ∧ v ∉ W)
    let fC (v : {v : Fin 48 // v ∈ C}) : {v : Fin 48 // v ∈ C} :=
      if h1 : v.val.val < 5 then
        ⟨⟨47 - v.val.val, by omega⟩, by
          revert v h1; decide⟩
      else if h2 : v.val.val ≥ 43 then
        ⟨⟨47 - v.val.val, by omega⟩, by
          revert v h1 h2; decide⟩
      else if h3 : 29 ≤ v.val.val ∧ v.val.val ≤ 42 then
        ⟨⟨71 - v.val.val, by omega⟩, by
          revert v h1 h2 h3; decide⟩
      else
        v
    have fC_inv (v : {v : Fin 48 // v ∈ C}) : fC (fC v) = v := by
      revert v; decide
    have fC_adj (v : {v : Fin 48 // v ∈ C}) :
        (op1957_shore_barrier_G.induce {x | x ∈ C}).Adj v (fC v) := by
      revert v; decide
    have hT : K₅.card % 2 = 1 := by decide
    have hN : W.card % 2 = 1 := by decide
    have hdisj : Disjoint K₅ W := by decide
    have hcross : ∀ a ∈ K₅, ∀ b ∈ W, ¬ op1957_shore_barrier_G.Adj a b := by decide
    have hsize : ({v : Fin 48 | v ∉ K₅ ∧ v ∉ W} : Set (Fin 48)).ncard = 2 * 12 := by
      have : ({v : Fin 48 | v ∉ K₅ ∧ v ∉ W} : Set (Fin 48)) = (C : Set (Fin 48)) := by
        ext x
        simp [C]
      rw [this, Set.ncard_coe_finset]
      decide
    have hPM : ∃ P : (op1957_shore_barrier_G.induce {v | v ∉ K₅ ∧ v ∉ W}).Subgraph, P.IsPerfectMatching := by
      have hEq : {v : Fin 48 | v ∉ K₅ ∧ v ∉ W} = {v | v ∈ C} := by
        ext x
        simp [C]
      rw [hEq]
      exact ⟨op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution _ fC fC_inv fC_adj,
        op1957_two_bridge_degree_only_shore_matching_obstruction_matchingOfInvolution_isPerfectMatching _ _ _ _⟩
    exact extendible_two_odd_anticomplete_shores_complement_unmatchable op1957_shore_barrier_G 12
      hExt K₅ W hT hN hdisj hcross hsize hPM
