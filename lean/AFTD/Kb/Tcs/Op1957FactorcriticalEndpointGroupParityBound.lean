import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FactorcriticalBlockOddGroupsInsideBound
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_factorcritical_endpoint_group_parity_bound

Topic: graphs   Node: 2a3be7bace6d

Provenance: helper lemma. OP-1957: boundary minimum-degree reduction, arXiv:2611.22690

For disjoint endpoint shores and mutually anticomplete barrier groups in a factor-critical block, provided the second shore meets the block, the number of odd block intersections of the first shore and barrier groups plus the block vertices in their union is at most the block size.
-/

theorem op1957_factorcritical_endpoint_group_parity_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B X Y : Finset V)
    (K : Finset I) (T : I → Finset V)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hXY : Disjoint X Y)
    (hXT : ∀ i ∈ K, Disjoint X (T i)) (hYT : ∀ i ∈ K, Disjoint Y (T i))
    (hTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j))
    (hantiXY : ∀ u ∈ X ∩ B, ∀ v ∈ Y ∩ B, ¬ G.Adj u v)
    (hantiXT : ∀ i ∈ K, ∀ u ∈ X, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiYT : ∀ i ∈ K, ∀ u ∈ Y, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v)
    (hYB : (Y ∩ B).Nonempty) :
    let R := X ∪ Y ∪ K.biUnion T
    (K.filter (fun i => Odd ((T i) ∩ B).card)).card +
      (if Odd ((X ∩ B).card) then 1 else 0) + (B ∩ R).card ≤ B.card := by
  classical
  dsimp only
  let R := X ∪ Y ∪ K.biUnion T
  let E := K.filter (fun i => Odd ((T i) ∩ B).card)
  let J : Finset (Option I) := E.image some ∪ (if Odd ((X ∩ B).card) then {none} else ∅)
  let F : Option I → Finset V := fun i => match i with
    | none => X ∩ B
    | some i => T i ∩ B
  have hEsub : E ⊆ K := Finset.filter_subset _ _
  have hJmem : ∀ i, some i ∈ J ↔ i ∈ E := by
    intro i
    by_cases ho : Odd ((X ∩ B).card) <;> simp [J,ho]
  have hJnone : none ∈ J ↔ Odd ((X ∩ B).card) := by
    by_cases ho : Odd ((X ∩ B).card) <;> simp [J,ho]
  have hsub : ∀ i ∈ J, F i ⊆ B ∩ R := by
    intro i hi u hu
    cases i with
    | none =>
      simp only [F,Finset.mem_inter] at hu
      exact Finset.mem_inter.mpr ⟨hu.2,Finset.mem_union_left _ (Finset.mem_union_left _ hu.1)⟩
    | some i =>
      have hiE := (hJmem i).mp hi
      have hiK := hEsub hiE
      simp only [F,Finset.mem_inter] at hu
      exact Finset.mem_inter.mpr ⟨hu.2,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hiK,hu.1⟩)⟩
  have hodd : ∀ i ∈ J, Odd (F i).card := by
    intro i hi
    cases i with
    | none => simpa [F] using (hJnone.mp hi)
    | some i => exact (Finset.mem_filter.mp ((hJmem i).mp hi)).2
  have hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j) := by
    intro i hi j hj hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        have hjK := hEsub ((hJmem j).mp hj)
        exact Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left (hXT j hjK))
    | some i =>
      have hiK := hEsub ((hJmem i).mp hi)
      cases j with
      | none =>
        exact Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left (hXT i hiK).symm)
      | some j =>
        have hjK := hEsub ((hJmem j).mp hj)
        have hij' : i ≠ j := by intro h; subst j; exact hij rfl
        exact Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left (hTT i hiK j hjK hij'))
  have hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ B ∩ R, v ∉ F i → ¬ G.Adj u v := by
    intro i hi u hu v hv hvF hadj
    have hvB := (Finset.mem_inter.mp hv).1
    have hvR := (Finset.mem_inter.mp hv).2
    have hvR' : v ∈ X ∪ Y ∪ K.biUnion T := hvR
    rcases Finset.mem_union.mp hvR' with hvXY | hvT
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · cases i with
        | none => exact hvF (Finset.mem_inter.mpr ⟨hvX,hvB⟩)
        | some i =>
          have hiK := hEsub ((hJmem i).mp hi)
          exact hantiXT i hiK v hvX u (Finset.mem_inter.mp hu).1 hadj.symm
      · cases i with
        | none => exact hantiXY u hu v (Finset.mem_inter.mpr ⟨hvY,hvB⟩) hadj
        | some i =>
          have hiK := hEsub ((hJmem i).mp hi)
          exact hantiYT i hiK v hvY u (Finset.mem_inter.mp hu).1 hadj.symm
    · obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hvT
      cases i with
      | none => exact hantiXT j hj u (Finset.mem_inter.mp hu).1 v hvj hadj
      | some i =>
        have hiK := hEsub ((hJmem i).mp hi)
        have hij : i ≠ j := by
          intro he; subst j
          exact hvF (Finset.mem_inter.mpr ⟨hvj,hvB⟩)
        exact hantiTT i hiK j hj hij u (Finset.mem_inter.mp hu).1 v hvj hadj
  obtain ⟨z,hz⟩ := hYB
  have hzY := (Finset.mem_inter.mp hz).1
  have hzB := (Finset.mem_inter.mp hz).2
  have hzR : z ∈ R := Finset.mem_union_left _ (Finset.mem_union_right _ hzY)
  have hz : ∀ i ∈ J, z ∉ F i := by
    intro i hi hzF
    cases i with
    | none => exact Finset.disjoint_left.mp hXY (Finset.mem_inter.mp hzF).1 hzY
    | some i =>
      have hiK := hEsub ((hJmem i).mp hi)
      exact Finset.disjoint_left.mp (hYT i hiK) hzY (Finset.mem_inter.mp hzF).1
  have hh := op1957_factorcritical_block_odd_groups_inside_bound G B R hcrit J F hsub hodd hdis hanti z hzB hzR hz
  have himage : (E.image some).card = E.card := Finset.card_image_iff.mpr (by
    intro x hx y hy hxy
    exact Option.some.inj hxy)
  have hJcard : J.card = E.card + (if Odd ((X ∩ B).card) then 1 else 0) := by
    by_cases ho : Odd ((X ∩ B).card)
    · simp [J,ho,himage]
    · simp [J,ho,himage]
  have hcard := Finset.card_sdiff_add_card_inter B R
  rw [hJcard] at hh
  change E.card + (if Odd ((X ∩ B).card) then 1 else 0) + (B ∩ R).card ≤ B.card
  omega
