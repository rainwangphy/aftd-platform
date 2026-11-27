import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierComponentPartition
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound
import AFTD.Kb.Tcs.FactorcriticalAnticompleteOddGroupsBound
import AFTD.Kb.Tcs.BoundaryFiveOddBlocksOneDefectComponentBarrierImpossible
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierPartitionWithOddEndpoints
import AFTD.Kb.Tcs.OddComponentsGroupIntoExactly
import AFTD.Kb.Tcs.ExtendibleEssentialEdgeAmbientOddShores
import AFTD.Kb.Tcs.Op1957AmbientOddShoresToComponentBarrier

/-!
# boundary_five_odd_blocks_one_defect_essential_edge_forces_two

Topic: graphs   Node: 70c466690c4f

Provenance: helper lemma. OP-1957: proposed uniform one-defect reduction for a five-vertex boundary block.

For an odd c with 5≤c≤k, consider the explicitly displayed order-4k four-block partition with |A|=5, |C|=c, factor-critical B, minimum degree at least 2k+2, and the stated 2k-separator property. If x in A has at most one nonneighbor in C, then every essential edge xy to y in C has at least two A vertices nonadjacent to y.
-/

theorem boundary_five_odd_blocks_one_defect_essential_edge_forces_two
    (k c : ℕ) (hc : 5 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=c)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hext : is_k_extendable G k) (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (hxy : G.Adj x y) (hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k)
    (hdefect : (C.filter (fun w => ¬ G.Adj x w)).card ≤ 1) :
    2 ≤ (A.filter (fun v => ¬ G.Adj v y)).card := by
  classical
  by_contra hn
  have hnon : (A.filter (fun v => ¬ G.Adj v y)).card ≤ 1 := by omega
  obtain ⟨X,Y,U,s,hXY,hXU,hYU,hxX,hyY,hoddX,hoddY,hsize,hUodd,hUpar,hcross,hantiX,hantiY⟩ :=
    extendible_essential_edge_ambient_odd_shores k G x y hxy hext hess
  have hsub : (X ∩ A).erase x ⊆ A.filter (fun v => ¬ G.Adj v y) := by
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hvX := (Finset.mem_inter.mp hv'.2).1
    have hvA := (Finset.mem_inter.mp hv'.2).2
    apply Finset.mem_filter.mpr
    refine ⟨hvA,?_⟩
    intro hadj
    exact hv'.1 (hcross v hvX y hyY hadj).1
  have hbad : (X ∩ A).card ≤ 2 := by
    have hx' : x ∈ X ∩ A := Finset.mem_inter.mpr ⟨hxX,hx⟩
    have hh := Finset.card_le_card hsub
    have he := Finset.card_erase_add_one hx'
    omega
  obtain ⟨Y',S,t,T,hxX',hyY',hXY',hXS,hYS,hXT,hYT,hST,hTT,hoddX',hoddY',hoddT,hS,hres,hcross',hcrossXT,hcrossYT,hcrossTT⟩ :=
    op1957_ambient_odd_shores_to_component_barrier k G X Y U s x y hXY hXU hYU hxX hyY
      hoddX hoddY hsize hUodd hUpar hcross hantiX hantiY
  exact boundary_five_odd_blocks_one_defect_component_barrier_impossible
    k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD
    hnoAB hnoCD hcritB hdegree hsep x y hx hy hxy hdefect X Y' S Finset.univ T hxX' hyY'
    hXY' hXS hYS (fun i _ => hXT i) (fun i _ => hYT i) (fun i _ => hST i)
    (fun i _ j _ hij => hTT i j hij) hoddX' hoddY' (fun i _ => hoddT i) (by simpa using hS)
    hres hcross' (fun i _ => hcrossXT i) (fun i _ => hcrossYT i)
    (fun i _ j _ hij => hcrossTT i j hij) hbad
