import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.BoundarySaturatedBlockCrossEdgeResidualReachable
import AFTD.Kb.Tcs.ForcedMatchingEdgeExcludesAdjacentTrueTwin
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierComponentPartition
import AFTD.Kb.Tcs.FactorcriticalAnticompleteOddComponentsBound
import AFTD.Kb.Tcs.BoundaryBarrierNumericContradictions
import AFTD.Kb.Tcs.Op1957SaturatedBOnlyConnectedShoreImpossible
import AFTD.Kb.Tcs.Op1957SaturatedForcedResidualSingleBlockVertex
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierPartitionConnectedEndpointShores
import AFTD.Kb.Tcs.GraphIsoOddComponentsCard
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# boundary_saturated_block_factorcritical_opposite_cross_removable

Topic: graphs   Node: 8149a370716d

Provenance: helper lemma. OP-1957; all-k forced-edge barrier reduction for a three-vertex non-factor-critical boundary component, session IN-1122.

Under the displayed four-block, saturation, separator, and degree hypotheses, if A has at least three vertices, B is factor-critical and the opposite block C has at most k vertices, a k-extendible graph remains k-extendible after deleting any A-to-C edge.
-/

theorem boundary_saturated_block_factorcritical_opposite_cross_removable
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hA : 3 ≤ A.card) (hC : C.card ≤ k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hAsat : ∀ a ∈ A, ∀ w ∈ A ∪ C ∪ D, a ≠ w → G.Adj a w)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hBcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hext : is_k_extendable G k)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C) (hxy : G.Adj x y) :
    is_k_extendable (G.deleteEdges {s(x,y)}) k := by
  classical
  by_contra hess
  obtain ⟨R,hR0,hxR,hyR,hP,hforced⟩ :=
    k_extendable_essential_edge_has_forced_matching_residual (4*k) k G x y hxy hext hess
  have hR : R.card=2*k := by omega
  let H := G.induce {v | v ∈ R}
  let x' : {v // v ∈ R} := ⟨x,hxR⟩
  let y' : {v // v ∈ R} := ⟨y,hyR⟩
  have hAR : A ∩ R = {x} := op1957_saturated_forced_residual_single_block_vertex G A B C D R
    hAB hAC hAD hBC hBD hCD hcover hnoAB hAsat x y hx hy hxR hyR hP hforced
  have hpath := boundary_saturated_block_cross_edge_residual_reachable k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hsizeAB hsizeCD hA hC hnoAB hnoCD hAsat hdegree hsep R hR x y hx hy hxy hxR hyR
  obtain ⟨S,X,Y,U,hSpos,hSX,hSY,hSU,hXY,hXU,hYU,hcoverR,hxX,hyY,hcross,hanti,hodd,hreachX,hreachY⟩ :=
    forced_matching_edge_barrier_partition_connected_endpoint_shores H x' y' hxy hP hforced hpath
  let f : {v // v ∈ R} ↪ Fin (4*k) := ⟨Subtype.val,Subtype.val_injective⟩
  let S' := S.map f
  let X' := X.map f
  let Y' := Y.map f
  let U' := U.map f
  have hmem (T : Finset {v // v ∈ R}) (z : {v // v ∈ R}) : z.val ∈ T.map f ↔ z ∈ T := by simp [f]
  have hd (T W : Finset {v // v ∈ R}) (h : Disjoint T W) : Disjoint (T.map f) (W.map f) := by
    apply Finset.disjoint_left.mpr
    intro z hzT hzW
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hzT
    obtain ⟨b,hb,he'⟩ := Finset.mem_map.mp hzW
    have hab : a=b := f.injective (he.trans he'.symm)
    exact Finset.disjoint_left.mp h ha (hab ▸ hb)
  have hsize : X'.card+Y'.card+U'.card+S'.card=2*k := by
    have h1 : Disjoint (S ∪ X) Y := Finset.disjoint_union_left.mpr ⟨hSY,hXY⟩
    have h2 : Disjoint (S ∪ X ∪ Y) U := Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hSU,hXU⟩,hYU⟩
    have hc := congrArg Finset.card hcoverR
    rw [Finset.card_union_of_disjoint h2,Finset.card_union_of_disjoint h1,Finset.card_union_of_disjoint hSX] at hc
    simp only [Finset.card_univ] at hc
    have hcardR : Fintype.card {v : Fin (4*k) | v ∈ R}=R.card := by simp
    rw [hcardR,hR] at hc
    simp [S',X',Y',U',Finset.card_map]
    omega
  have hs : 1 ≤ S'.card := by
    have hh := Finset.card_pos.mpr hSpos
    simp only [S',Finset.card_map]
    omega
  have hxX' : x ∈ X' := (hmem X x').2 hxX
  have hyY' : y ∈ Y' := (hmem Y y').2 hyY
  have hXsub : X' ⊆ R := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hz
    exact a.property
  have hXAdis : X' ∩ A = {x} := by
    ext z
    constructor
    · intro hz
      have hzX := (Finset.mem_inter.mp hz).1
      have hzA := (Finset.mem_inter.mp hz).2
      have hzAR : z ∈ A ∩ R := Finset.mem_inter.mpr ⟨hzA,hXsub hzX⟩
      rw [hAR] at hzAR
      exact hzAR
    · intro hz
      have he := Finset.mem_singleton.mp hz
      subst z
      exact Finset.mem_inter.mpr ⟨hxX',hx⟩
  have hcross' : ∀ a ∈ X', ∀ b ∈ Y', G.Adj a b → a=x ∧ b=y := by
    intro a ha b hb hab
    obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
    have hh := hcross a' ha' b' hb' hab
    exact ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩
  have hantiX : ∀ a ∈ X', ∀ u ∈ U', ¬ G.Adj a u := by
    intro a ha u hu hadj
    obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
    exact hanti u' hu' a' (Finset.mem_union_left _ ha') hadj.symm
  have hantiY : ∀ b ∈ Y', ∀ u ∈ U', ¬ G.Adj b u := by
    intro b hb u hu hadj
    obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
    exact hanti u' hu' b' (Finset.mem_union_right _ hb') hadj.symm
  have hXU' := hd X U hXU
  have hXY' := hd X Y hXY
  have hYU' := hd Y U hYU
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hy
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hx h
  have hsubset (z : Fin (4*k)) (hzB : z ∉ B) : z ∈ A ∪ C ∪ D := by
    have h := show z ∈ A ∪ B ∪ C ∪ D by rw [hcover]; simp
    simp only [Finset.mem_union] at h ⊢
    rcases h with ((ha | hb) | hc') | hd'
    · exact Or.inl (Or.inl ha)
    · exact False.elim (hzB hb)
    · exact Or.inl (Or.inr hc')
    · exact Or.inr hd'
  have hUB : U' ⊆ B := by
    intro z hz
    by_contra hzB
    have hzx : z ≠ x := fun he => Finset.disjoint_left.mp hXU' hxX' (he ▸ hz)
    have hadj := hAsat x hx z (hsubset z hzB) hzx.symm
    exact hantiX x hxX' z hz hadj
  have hY : Y' ⊆ B ∪ {y} := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Finset.mem_union_left _ hzB
    · have hzx : z ≠ x := fun he => Finset.disjoint_left.mp hXY' hxX' (he ▸ hz)
      have hadj := hAsat x hx z (hsubset z hzB) hzx.symm
      have he := (hcross' x hxX' z hz hadj).2
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr he)
  let eU : (H.induce {v | v ∈ U}) ≃g (G.induce {v | v ∈ U'}) := {
    toFun := fun a => ⟨a.val.val,(hmem U a.val).2 a.property⟩
    invFun := fun a => ⟨⟨a.val,by obtain ⟨w,hw,he⟩ := Finset.mem_map.mp a.property; exact he ▸ w.property⟩,
      by
        have haU : a.val ∈ U.map f := by simpa [U'] using a.property
        exact (hmem U _).1 haU⟩
    left_inv := fun a => by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := fun a => by apply Subtype.ext; rfl
    map_rel_iff' := by rfl }
  have hiso := graph_iso_odd_components_card _ _ eU
  have hodd' : S'.card ≤ (G.induce {v | v ∈ U'}).oddComponents.ncard := by
    rw [← hiso]
    simpa [S'] using hodd
  let eX : (H.induce {v | v ∈ X}) →g (G.induce {v | v ∈ X'}) := {
    toFun := fun a => ⟨a.val.val,(hmem X a.val).2 a.property⟩
    map_rel' := by intro a b h; exact h }
  have hreach' : ∀ z (hz : z ∈ X'), (G.induce {a | a ∈ X'}).Reachable ⟨x,hxX'⟩ ⟨z,hz⟩ := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hz
    have hh := SimpleGraph.Reachable.map eX (hreachX a ha)
    simpa [eX,x',f] using hh
  have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hy h
  have hsubN : G.neighborFinset y ⊆ ((Finset.univ \ D).erase y) := by
    intro z hz
    have hyz : G.Adj y z := by simpa using hz
    simp only [Finset.mem_erase,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact ⟨hyz.ne.symm,fun hzD => hnoCD y hy z hzD hyz⟩
  have hNcard := Finset.card_le_card hsubN
  have hUcard : ((Finset.univ : Finset (Fin (4*k))) \ D).card=2*k+C.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),Finset.card_univ,Fintype.card_fin]
    omega
  have hyout : y ∈ (Finset.univ : Finset (Fin (4*k))) \ D := by simp [hyD]
  rw [Finset.card_erase_of_mem hyout,hUcard] at hNcard
  have hc : 3 ≤ C.card := by have hh := hdegree y; omega
  exact op1957_saturated_b_only_connected_shore_impossible G k C.card S'.card hc hC (by simp) A B C D X' Y' U'
    hAB hAC hAD hBC hBD hCD hcover hA hsizeAB rfl hsizeCD hnoAB hnoCD hBcrit hdegree hsep
    x y hx hy hxX' hyY' hXY' hXU' hYU' hXAdis hY hUB hsize hs hodd' hcross' hantiX hantiY hreach'
