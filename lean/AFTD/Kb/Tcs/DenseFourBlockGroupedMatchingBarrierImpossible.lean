import AFTD.Prelude
import AFTD.Kb.Tcs.GroupVertexDegreeBudget
import AFTD.Kb.Tcs.DenseFourBlockMatchingBarrierArithmetic

/-!
# dense_four_block_grouped_matching_barrier_impossible

Topic: graphs   Node: fea4cafea96a

Provenance: helper lemma. OP-1957; graph-to-count transfer for the deleted-four-block matching obstruction.

The displayed grouped odd-component barrier is incompatible with the four-block degree and separator counts.
-/

set_option maxHeartbeats 2000000

theorem dense_four_block_grouped_matching_barrier_impossible
    (k : ℕ) (hk : 7 ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D U D₀ S : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : 7 ≤ C.card)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hUB : U ⊆ B) (hUD : D₀ ⊆ D) (hUcard : U.card ≤ k-4) (hsmall : U.card+D₀.card ≤ k)
    (hSZ : Disjoint S (U ∪ (A ∪ D₀)))
    (hslo : 2*k ≤ S.card+U.card+D₀.card+5)
    (q : ℕ) (F : Fin q → Finset (Fin (4*k)))
    (hodd : ∀ i, Odd (F i).card)
    (hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hFS : ∀ i, Disjoint (F i) S)
    (hFZ : ∀ i, Disjoint (F i) (U ∪ (A ∪ D₀)))
    (hcover : ((Finset.univ : Finset (Fin q)).biUnion F) ∪ S ∪ (U ∪ (A ∪ D₀)) = Finset.univ)
    (hclosed : ∀ i v, v ∈ F i → ∀ w, G.Adj v w →
      w ∈ F i ∨ w ∈ S ∨ w ∈ U ∪ (A ∪ D₀))
    (hq : 2*k+S.card ≤ q+U.card+D₀.card+3) : False := by
  classical
  let Z := U ∪ (A ∪ D₀)
  let H := (Finset.univ : Finset (Fin q)).biUnion F
  have hUA : Disjoint U A := Finset.disjoint_of_subset_left hUB hAB.symm
  have hUDdis : Disjoint U D₀ := Finset.disjoint_of_subset_left hUB
    (Finset.disjoint_of_subset_right hUD hBD)
  have hADdis : Disjoint A D₀ := Finset.disjoint_of_subset_right hUD hAD
  have hZcard : Z.card = U.card+D₀.card+5 := by
    dsimp [Z]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hUA,hUDdis⟩),
      Finset.card_union_of_disjoint hADdis,hA]
    omega
  have hHS : Disjoint H S := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hFS i) hvi hs
  have hHZ : Disjoint H Z := by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hFZ i) hvi hz
  have hHScard : Disjoint (H ∪ S) Z := Finset.disjoint_union_left.mpr ⟨hHZ,hSZ⟩
  have htotal : (∑ i : Fin q, (F i).card) + S.card+U.card+D₀.card+5 = 4*k := by
    have hp : ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint F := by
      intro i _ j _ hij
      exact hFdis i j hij
    have hh := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hHScard,Finset.card_union_of_disjoint hHS,
      Finset.card_biUnion hp] at hh
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    rw [hZcard] at hh
    omega
  have hFpos : ∀ i, 1 ≤ (F i).card := by
    intro i
    obtain ⟨t,ht⟩ := hodd i
    omega
  have hqle : q ≤ ∑ i : Fin q, (F i).card := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun i _ => hFpos i)
    simpa using hh
  have hshi : S.card ≤ k-1 := by omega
  have hgroupdegree (i : Fin q) (v : Fin (4*k)) (hv : v ∈ F i) :
      (G.neighborFinset v).card + 1 ≤ (F i).card + S.card + Z.card :=
    group_vertex_degree_budget G (F i) S Z v hv (hclosed i v hv)
  have hnosingle : S.card ≤ k-4 → ∀ i, 2 ≤ (F i).card := by
    intro hs i
    have hfpos : 0 < (F i).card := by have hi := hFpos i; omega
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hfpos
    have hh := hgroupdegree i v hv
    have hd := hdegree v
    omega
  let T : Finset (Fin (4*k)) := ((B \ U) ∪ C) \ S
  have hBUs : B \ U ⊆ B := Finset.sdiff_subset
  have hBUC : Disjoint (B \ U) C := Finset.disjoint_of_subset_left hBUs hBC
  have hBUcard : (B \ U).card+U.card = 2*k-5 := by
    rw [Finset.card_sdiff_of_subset hUB,hB]
    omega
  have hTlow : 7 ≤ T.card := by
    have hh := Finset.card_sdiff_add_card_inter ((B \ U) ∪ C) S
    have hi : (((B \ U) ∪ C) ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
    have hu : ((B \ U) ∪ C).card = (B \ U).card+C.card := Finset.card_union_of_disjoint hBUC
    dsimp [T]
    omega
  have hTZ : Disjoint T Z := by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    have hv' := (Finset.mem_sdiff.mp hv).1
    rcases Finset.mem_union.mp hv' with hb | hc
    · have hbB := (Finset.mem_sdiff.mp hb).1
      have hbU := (Finset.mem_sdiff.mp hb).2
      rcases Finset.mem_union.mp hz with hu | hz
      · exact hbU hu
      · rcases Finset.mem_union.mp hz with ha | hd
        · exact Finset.disjoint_left.mp hAB ha hbB
        · exact Finset.disjoint_left.mp hBD hbB (hUD hd)
    · rcases Finset.mem_union.mp hz with hu | hz
      · exact Finset.disjoint_left.mp hBC (hUB hu) hc
      · rcases Finset.mem_union.mp hz with ha | hd
        · exact Finset.disjoint_left.mp hAC ha hc
        · exact Finset.disjoint_left.mp hCD hc (hUD hd)
  have hTinH : T ⊆ H := by
    intro v hv
    have hvall : v ∈ H ∪ S ∪ Z := by rw [hcover]; simp
    rcases Finset.mem_union.mp hvall with hvHS | hvZ
    · rcases Finset.mem_union.mp hvHS with hvH | hvS
      · exact hvH
      · exact False.elim ((Finset.mem_sdiff.mp hv).2 hvS)
    · exact False.elim (Finset.disjoint_left.mp hTZ hv hvZ)
  have hUDis : Disjoint U D₀ := hUDdis
  have hUAcard : (U ∪ A).card = U.card+5 := by
    rw [Finset.card_union_of_disjoint hUA,hA]
  have hUDcard : (U ∪ D₀).card = U.card+D₀.card := by
    rw [Finset.card_union_of_disjoint hUDis]
  have hlargegroup : ∀ i, ∀ v ∈ F i, v ∈ (B \ U) ∪ C → 3 ≤ (F i).card := by
    intro i v hv hvBC
    have hvcover := hclosed i v hv
    rcases Finset.mem_union.mp hvBC with hvB | hvC
    · have hvB' := (Finset.mem_sdiff.mp hvB).1
      have hallowed : ∀ w, G.Adj v w → w ∈ F i ∨ w ∈ S ∨ w ∈ U ∪ D₀ := by
        intro w hadj
        rcases hvcover w hadj with hf | hs | hz
        · exact Or.inl hf
        · exact Or.inr (Or.inl hs)
        · rcases Finset.mem_union.mp hz with hu | hz
          · exact Or.inr (Or.inr (Finset.mem_union_left _ hu))
          · rcases Finset.mem_union.mp hz with ha | hd
            · exact False.elim (hnoAB w ha v hvB' hadj.symm)
            · exact Or.inr (Or.inr (Finset.mem_union_right _ hd))
      have hh := group_vertex_degree_budget G (F i) S (U ∪ D₀) v hv hallowed
      have hd := hdegree v
      omega
    · have hallowed : ∀ w, G.Adj v w → w ∈ F i ∨ w ∈ S ∨ w ∈ U ∪ A := by
        intro w hadj
        rcases hvcover w hadj with hf | hs | hz
        · exact Or.inl hf
        · exact Or.inr (Or.inl hs)
        · rcases Finset.mem_union.mp hz with hu | hz
          · exact Or.inr (Or.inr (Finset.mem_union_left _ hu))
          · rcases Finset.mem_union.mp hz with ha | hd
            · exact Or.inr (Or.inr (Finset.mem_union_right _ ha))
            · exact False.elim (hnoCD v hvC w (hUD hd) hadj)
      have hh := group_vertex_degree_budget G (F i) S (U ∪ A) v hv hallowed
      have hd := hdegree v
      omega
  let J : Finset (Fin q) := Finset.univ.filter (fun i => 3 ≤ (F i).card)
  have hTJ : T ⊆ J.biUnion F := by
    intro v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp (hTinH hv)
    have hlarge := hlargegroup i v hvi (Finset.mem_sdiff.mp hv).1
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hlarge⟩,hvi⟩
  have hsum : T.card ≤ ∑ i : Fin q, if 3 ≤ (F i).card then (F i).card else 0 := by
    have hh := (Finset.card_le_card hTJ).trans (Finset.card_biUnion_le)
    simpa [J,Finset.sum_filter] using hh
  apply dense_four_block_matching_barrier_arithmetic k U.card D₀.card S.card q (fun i => (F i).card)
    hk hUcard hsmall hslo hshi hq hodd htotal hnosingle
  intro _
  omega
