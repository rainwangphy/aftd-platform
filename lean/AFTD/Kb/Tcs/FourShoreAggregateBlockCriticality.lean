import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.Op1957FourShoreAggregateTotals
import AFTD.Kb.Tcs.Op1957FactorcriticalBlockTwoFamilyCount

/-!
# four_shore_aggregate_block_criticality

Topic: graphs   Node: 444b671f691e

Provenance: helper lemma. OP-1957; positive-separator factor-critical block count transfer.

Under the displayed disjoint shore, pooled odd-group and connected factor-critical block assumptions, the aggregate B counts satisfy both the outside-vertex and full-block inequalities.
-/

set_option maxHeartbeats 2000000

theorem four_shore_aggregate_block_criticality
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F B : Fin 4 → Finset V) (E : Finset V) (x y : V)
    (T : Finset J) (Q : J → Finset V)
    (hFdis : ∀ i j : Fin 4, i ≠ j → Disjoint (F i) (F j))
    (hEdis : ∀ i : Fin 4, Disjoint (F i) E)
    (hBdis : ∀ i j : Fin 4, i ≠ j → Disjoint (B i) (B j))
    (hBcover : (Finset.univ : Finset (Fin 4)).biUnion B = Finset.univ)
    (hEB : E ⊆ B 1) (hx : x ∈ B 0) (hy : y ∈ B 2)
    (hcross : ∀ i l : Fin 4, i ≠ l → ∀ a ∈ F i, ∀ b ∈ F l, G.Adj a b →
      (i=0 ∧ l=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ l=0 ∧ a=y ∧ b=x))
    (hEanti : ∀ i : Fin 4, ∀ a ∈ F i, ∀ w ∈ E, ¬ G.Adj a w)
    (hQodd : ∀ j ∈ T, Odd (Q j).card)
    (hQdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (Q i) (Q j))
    (hQanti : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ a ∈ Q i, ∀ b ∈ Q j, ¬ G.Adj a b)
    (hQcover : T.biUnion Q = E)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B 1}) 1)
    (hconn : (G.induce {v | v ∈ B 1}).Connected) :
    let g : Fin 4 → Fin 4 → ℕ := fun i b => (F i ∩ B b).card
    let tot := (∑ i : Fin 4, g i 1) + E.card
    (tot < (B 1).card → T.card + tot + 1 ≤ (B 1).card) ∧
    (tot = (B 1).card → T.card ≤ 1 ∧
      (∑ i : Fin 4, if 1 ≤ g i 1 then 1 else 0) + T.card ≤ 1) := by
  classical
  dsimp only
  let R := (Finset.univ : Finset (Fin 4)).biUnion F ∪ E
  let P : Fin 4 → Finset V := fun i => F i ∩ B 1
  have hQsubE : ∀ i ∈ T, Q i ⊆ E := by
    intro i hi v hv
    rw [←hQcover]
    exact Finset.mem_biUnion.mpr ⟨i,hi,hv⟩
  have hPsub : ∀ i ∈ (Finset.univ : Finset (Fin 4)), P i ⊆ B 1 ∩ R := by
    intro i _ v hv
    obtain ⟨hvF,hvB⟩ := Finset.mem_inter.mp hv
    refine Finset.mem_inter.mpr ⟨hvB,Finset.mem_union_left _ ?_⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hvF⟩
  have hQsub : ∀ i ∈ T, Q i ⊆ B 1 ∩ R := by
    intro i hi v hv
    have hvE := hQsubE i hi hv
    exact Finset.mem_inter.mpr ⟨hEB hvE,Finset.mem_union_right _ hvE⟩
  have hQne : ∀ i ∈ T, (Q i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    have hh := hQodd i hi
    obtain ⟨n,hn⟩ := hh
    omega
  have hPdis : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      i ≠ j → Disjoint (P i) (P j) := by
    intro i _ j _ hij
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hFdis i j hij))
  have hPQdis : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ T, Disjoint (P i) (Q j) := by
    intro i _ j hj
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right (hQsubE j hj) (hEdis i))
  have hxB : x ∉ B 1 := fun h => Finset.disjoint_left.mp (hBdis 0 1 (by decide)) hx h
  have hyB : y ∉ B 1 := fun h => Finset.disjoint_left.mp (hBdis 2 1 (by decide)) hy h
  have hPanti : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, ¬ G.Adj a b := by
    intro i _ j _ hij a ha b hb hadj
    rcases hcross i j hij a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1 hadj with h | h
    · exact hxB (h.2.2.1 ▸ (Finset.mem_inter.mp ha).2)
    · exact hyB (h.2.2.1 ▸ (Finset.mem_inter.mp ha).2)
  have hPQanti : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ T,
      ∀ a ∈ P i, ∀ b ∈ Q j, ¬ G.Adj a b := by
    intro i _ j hj a ha b hb
    exact hEanti i a (Finset.mem_inter.mp ha).1 b (hQsubE j hj hb)
  have hcover : (Finset.univ : Finset (Fin 4)).biUnion P ∪ T.biUnion Q = B 1 ∩ R := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hvP | hvQ
      · obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hvP
        exact hPsub i hi hvi
      · rw [hQcover] at hvQ
        exact Finset.mem_inter.mpr ⟨hEB hvQ,Finset.mem_union_right _ hvQ⟩
    · intro hv
      obtain ⟨hvB,hvR⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvR with hvF | hvE
      · obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hvF
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_inter.mpr ⟨hvi,hvB⟩⟩)
      · apply Finset.mem_union_right
        rw [hQcover]
        exact hvE
  have htots := op1957_four_shore_aggregate_totals F B E hFdis hEdis hBdis hBcover hEB
  have htot : (∑ i : Fin 4, (F i ∩ B 1).card) + E.card = (B 1 ∩ R).card := by
    have hh := htots.1 (1 : Fin 4)
    simpa [R,Finset.inter_comm] using hh
  have hg : ((Finset.univ : Finset (Fin 4)).filter (fun i => (P i).Nonempty)).card =
      ∑ i : Fin 4, if 1 ≤ (F i ∩ B 1).card then 1 else 0 := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    have he : (P i).Nonempty ↔ 1 ≤ (F i ∩ B 1).card := by
      simpa only [P] using (Finset.one_le_card : 1 ≤ (F i ∩ B 1).card ↔ (F i ∩ B 1).Nonempty).symm
    by_cases h : (P i).Nonempty
    · rw [if_pos h,if_pos (he.mp h)]
    · rw [if_neg h,if_neg (fun hh => h (he.mpr hh))]
  have hh := op1957_factorcritical_block_two_family_count G (B 1) R hcrit hconn
    Finset.univ T P Q hPsub hQsub hQne hQodd hPdis hQdis hPQdis hPanti hQanti hPQanti hcover
  rw [hg] at hh
  rw [htot]
  exact hh
