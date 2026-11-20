import AFTD.Prelude

/-!
# degree_nine_four_bridge_groups_bound

Topic: graphs   Node: 17c06091f9b0

Provenance: helper lemma. The d=9 pair-intersection degree contradiction in the OP-1957 crossing-cut route.

Suppose a finite graph has maximum degree nine. An indexed family has vertex sets Q(i) of size at most six, with every two distinct sets meeting in four vertices, and distinct endpoints z(i), each adjacent to all of Q(i). For each pair i,j, all vertices of Q(i)∩Q(j) are adjacent to a six-vertex set containing no endpoint. Then there are at most four indices.
-/

theorem in1076_four_groups
    {I V : Type*} [DecidableEq I] [DecidableEq V] (F : Finset I) (Q : I → Finset V)
    (hsize : ∀ i ∈ F, (Q i).card ≤ 6)
    (hpair : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (Q i ∩ Q j).card = 4)
    (hload : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ q ∈ Q i ∩ Q j,
      (((F.erase i).erase j).filter (fun l => q ∈ Q l)).card ≤ 1) :
    F.card ≤ 4 := by
  classical
  by_cases hsmall : F.card ≤ 1
  · omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  let R := Q i ∩ Q j
  let T := (F.erase i).erase j
  have hR : R.card = 4 := hpair i hi j hj hij
  have hj' : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hT : T.card + 2 = F.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hother : ∀ l ∈ T, l ∈ F ∧ l ≠ i ∧ l ≠ j := by
    intro l hl
    simp only [T, Finset.mem_erase] at hl
    exact ⟨hl.2.2, hl.2.1, hl.1⟩
  have htwo : ∀ l ∈ T, 2 ≤ (R ∩ Q l).card := by
    intro l hl
    obtain ⟨hlF, hli, hlj⟩ := hother l hl
    have hil : i ≠ l := hli.symm
    have hcard := Finset.card_inter_add_card_union (Q i ∩ Q j) (Q i ∩ Q l)
    have hunion : ((Q i ∩ Q j) ∪ (Q i ∩ Q l)).card ≤ (Q i).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
    have heq : (Q i ∩ Q j) ∩ (Q i ∩ Q l) = R ∩ Q l := by
      ext x
      simp [R] <;> tauto
    rw [heq, hpair i hi j hj hij, hpair i hi l hlF hil] at hcard
    have hqi := hsize i hi
    omega
  have hswap : (∑ l ∈ T, (R ∩ Q l).card) =
      ∑ q ∈ R, (T.filter (fun l => q ∈ Q l)).card := by
    calc
      (∑ l ∈ T, (R ∩ Q l).card) =
          ∑ l ∈ T, ∑ q ∈ R, if q ∈ Q l then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [← Finset.card_filter]
            congr 1
      _ = ∑ q ∈ R, ∑ l ∈ T, if q ∈ Q l then 1 else 0 := Finset.sum_comm
      _ = ∑ q ∈ R, (T.filter (fun l => q ∈ Q l)).card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.card_filter]
  have hlower := Finset.sum_le_sum htwo
  have hconstant : (∑ l ∈ T, (2 : ℕ)) = T.card * 2 := by simp
  rw [hconstant, hswap] at hlower
  have hupper : (∑ q ∈ R, (T.filter (fun l => q ∈ Q l)).card) ≤ ∑ q ∈ R, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hload i hi j hj hij q hq
  have hconstant' : (∑ q ∈ R, (1 : ℕ)) = R.card := by simp
  rw [hconstant', hR] at hupper
  omega

theorem degree_nine_four_bridge_groups_bound
    {I V : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (H : SimpleGraph V) [DecidableRel H.Adj] (F : Finset I)
    (Q : I → Finset V) (z : I → V) (K : I → I → Finset V)
    (hsize : ∀ i ∈ F, (Q i).card ≤ 6)
    (hpair : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (Q i ∩ Q j).card = 4)
    (hinj : ∀ i ∈ F, ∀ j ∈ F, z i = z j → i = j)
    (hK : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (K i j).card = 6 ∧
      (∀ l ∈ F, z l ∉ K i j) ∧
      (∀ q ∈ Q i ∩ Q j, ∀ w ∈ K i j, H.Adj q w))
    (hz : ∀ i ∈ F, ∀ q ∈ Q i, H.Adj q (z i))
    (hdegree : ∀ q, (H.neighborFinset q).card ≤ 9) : F.card ≤ 4 := by
  classical
  apply in1076_four_groups F Q hsize hpair
  intro i hi j hj hij q hq
  let T := (((F.erase i).erase j).filter (fun l => q ∈ Q l))
  by_contra hn
  change ¬ T.card ≤ 1 at hn
  have hT : 1 < T.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hT
  have ha' : a ∈ F ∧ a ≠ i ∧ a ≠ j ∧ q ∈ Q a := by
    simp only [T, Finset.mem_filter, Finset.mem_erase] at ha
    exact ⟨ha.1.2.2, ha.1.2.1, ha.1.1, ha.2⟩
  have hb' : b ∈ F ∧ b ≠ i ∧ b ≠ j ∧ q ∈ Q b := by
    simp only [T, Finset.mem_filter, Finset.mem_erase] at hb
    exact ⟨hb.1.2.2, hb.1.2.1, hb.1.1, hb.2⟩
  have hzij : z i ≠ z j := by intro he; exact hij (hinj i hi j hj he)
  have hzia : z i ≠ z a := by intro he; exact ha'.2.1 (hinj i hi a ha'.1 he).symm
  have hzib : z i ≠ z b := by intro he; exact hb'.2.1 (hinj i hi b hb'.1 he).symm
  have hzja : z j ≠ z a := by intro he; exact ha'.2.2.1 (hinj j hj a ha'.1 he).symm
  have hzjb : z j ≠ z b := by intro he; exact hb'.2.2.1 (hinj j hj b hb'.1 he).symm
  have hzab : z a ≠ z b := by intro he; exact hab (hinj a ha'.1 b hb'.1 he)
  let Z : Finset V := {z i, z j, z a, z b}
  have hZ : Z.card = 4 := by simp [Z, hzij, hzia, hzib, hzja, hzjb, hzab]
  have hKZ : Disjoint (K i j) Z := by
    apply Finset.disjoint_left.mpr
    intro x hxK hxZ
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hxZ
    rcases hxZ with rfl | rfl | rfl | rfl
    · exact (hK i hi j hj hij).2.1 i hi hxK
    · exact (hK i hi j hj hij).2.1 j hj hxK
    · exact (hK i hi j hj hij).2.1 a ha'.1 hxK
    · exact (hK i hi j hj hij).2.1 b hb'.1 hxK
  have hsub : K i j ∪ Z ⊆ H.neighborFinset q := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hx with hxK | hxZ
    · exact (hK i hi j hj hij).2.2 q hq x hxK
    · simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hxZ
      rcases hxZ with rfl | rfl | rfl | rfl
      · exact hz i hi q (Finset.mem_inter.mp hq).1
      · exact hz j hj q (Finset.mem_inter.mp hq).2
      · exact hz a ha'.1 q ha'.2.2.2
      · exact hz b hb'.1 q hb'.2.2.2
  have hc := (Finset.card_le_card hsub).trans (hdegree q)
  rw [Finset.card_union_of_disjoint hKZ, (hK i hi j hj hij).1, hZ] at hc
  omega
