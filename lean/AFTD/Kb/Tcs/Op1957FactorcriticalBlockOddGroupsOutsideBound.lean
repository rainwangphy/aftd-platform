import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalOddGroupsOutsideVertexBound
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_factorcritical_block_odd_groups_outside_bound

Topic: graphs   Node: 286f675d2660

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Factorcritical block odd groups outside bound.
-/

set_option maxHeartbeats 2000000

theorem op1957_factorcritical_block_odd_groups_outside_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B R : Finset V)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (J : Finset I) (F : I → Finset V)
    (hsub : ∀ i ∈ J, F i ⊆ B ∩ R)
    (hodd : ∀ i ∈ J, Odd (F i).card)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ B ∩ R, v ∉ F i → ¬ G.Adj u v)
    (z : V) (hzB : z ∈ B) (hzR : z ∉ R) :
    J.card + 1 ≤ (B \ R).card := by
  classical
  let H := G.induce {v | v ∈ B}
  let L : Finset {v // v ∈ B} := R.subtype (· ∈ B)
  let Q : I → Finset {v // v ∈ B} := fun i => (F i).subtype (· ∈ B)
  have hQsub : ∀ i ∈ J, Q i ⊆ L := by
    intro i hi u hu
    have huF : u.val ∈ F i := by simpa [Q] using hu
    have huR : u.val ∈ R := (Finset.mem_inter.mp (hsub i hi huF)).2
    simpa [L] using huR
  have hQodd : ∀ i ∈ J, Odd (Q i).card := by
    intro i hi
    have he : (F i).filter (· ∈ B) = F i := Finset.filter_true_of_mem (by
      intro u hu
      exact (Finset.mem_inter.mp (hsub i hi hu)).1)
    simpa [Q,Finset.card_subtype,he] using hodd i hi
  have hQdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    have hui' : u.val ∈ F i := by simpa [Q] using hui
    have huj' : u.val ∈ F j := by simpa [Q] using huj
    exact Finset.disjoint_left.mp (hdis i hi j hj hij) hui' huj'
  have hQanti : ∀ i ∈ J, ∀ u ∈ Q i, ∀ v ∈ L, v ∉ Q i → ¬ H.Adj u v := by
    intro i hi u hu v hv hvQ hadj
    have huF : u.val ∈ F i := by simpa [Q] using hu
    have hvR : v.val ∈ R := by simpa [L] using hv
    have hvF : v.val ∉ F i := by simpa [Q] using hvQ
    exact hanti i hi u.val huF v.val (Finset.mem_inter.mpr ⟨v.property,hvR⟩) hvF hadj
  let z' : {v // v ∈ B} := ⟨z,hzB⟩
  have hzL : z' ∉ L := by simpa [L,z'] using hzR
  have hh := factorcritical_odd_groups_outside_vertex_bound H hcrit J Q L
    hQsub hQodd hQdis hQanti z' hzL
  have hset : (Finset.univ : Finset {v // v ∈ B}) \ L = (B \ R).subtype (· ∈ B) := by
    ext v
    simp [L,v.property]
  rw [hset,Finset.card_subtype] at hh
  have he : (B \ R).filter (· ∈ B) = B \ R := Finset.filter_true_of_mem (by
    intro v hv
    exact (Finset.mem_sdiff.mp hv).1)
  simpa [he] using hh
