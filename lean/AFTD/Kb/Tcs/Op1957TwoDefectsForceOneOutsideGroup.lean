import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# op1957_two_defects_force_one_outside_group

Topic: graphs   Node: 6f0bace71237

Provenance: helper lemma. OP-1957: boundary minimum-degree reduction, arXiv:2611.22690

If a vertex outside B is anticomplete to B and has at most two nonneighbors outside B, and it misses two distinct specified outside vertices, then every other anticomplete group avoiding those two vertices lies in B.
-/

theorem op1957_two_defects_force_one_outside_group
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V)
    (d : ℕ) (hsize : Fintype.card V = B.card + d + 1)
    (K : Finset I) (T : I → Finset V) (i : I) (hi : i ∈ K)
    (hanti : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ w ∈ T i, ∀ z ∈ T j, ¬ G.Adj w z)
    (w x y : V) (hw : w ∈ T i) (hwB : w ∉ B)
    (hB : ∀ b ∈ B, ¬ G.Adj w b)
    (hdegree : d ≤ (G.neighborFinset w).card + 2)
    (hxB : x ∉ B) (hyB : y ∉ B)
    (hwx : x ≠ w) (hwy : y ≠ w) (hxy : x ≠ y)
    (hnx : ¬ G.Adj w x) (hny : ¬ G.Adj w y)
    (hxT : ∀ j ∈ K, x ∉ T j) (hyT : ∀ j ∈ K, y ∉ T j)
    (hdis : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j)) :
    ∀ j ∈ K, i ≠ j → T j ⊆ B := by
  classical
  have hbound := anticomplete_neighbor_defect_bound G B w hwB hB d 2 hsize hdegree
  intro j hj hij z hz
  by_contra hzB
  have hzw : z ≠ w := by
    intro he
    subst z
    exact Finset.disjoint_left.mp (hdis i hi j hj hij) hw hz
  have hzx : z ≠ x := by intro he; subst z; exact hxT j hj hz
  have hzy : z ≠ y := by intro he; subst z; exact hyT j hj hz
  have hnz := hanti i hi j hj hij w hw z hz
  have hsub : ({x,y,z} : Finset V) ⊆ (((Finset.univ \ B).erase w) \ G.neighborFinset w) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [hwx,hxB,hnx]
    · simp [hwy,hyB,hny]
    · simp [hzw,hzB,hnz]
  have hc := Finset.card_le_card hsub
  have hcard : ({x,y,z} : Finset V).card = 3 := by simp [hxy,hzx,hzy,hxy.symm,hzx.symm,hzy.symm]
  omega
