import AFTD.Prelude

/-!
# op1957_exceptional_slots_four_shore_structure

Topic: graphs   Node: 178e1cd771fc

Provenance: helper lemma. OP-1957 small-shore barrier graph-to-count transfer

A pairwise anticomplete barrier partition, split into two exceptional groups and a pool, produces four pairwise disjoint shores with the same unique crossing edge and an anticomplete pool.
-/

theorem op1957_exceptional_slots_four_shore_structure
    {I V : Type*} [DecidableEq I] [DecidableEq V] (G : SimpleGraph V)
    (K J : Finset I) (R : I → Finset V) (U X Y P Q : Finset V) (x y : V)
    (hJK : J ⊆ K)
    (hsub : ∀ i ∈ K, R i ⊆ U)
    (hne : ∀ i ∈ K, (R i).Nonempty)
    (hdis : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (R i) (R j))
    (hanti : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j, ¬ G.Adj u v)
    (hcover : K.biUnion R = U)
    (hP : P = ∅ ∨ ∃ i ∈ K \ J, P = R i)
    (hQ : Q = ∅ ∨ ∃ i ∈ K \ J, Q = R i)
    (hslot : ∀ i ∈ K \ J, R i = P ∨ R i = Q)
    (hPQ : Disjoint P Q)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hXanti : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hYanti : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u) :
    let F : Fin 4 → Finset V := ![X,Y,P,Q]
    let E := J.biUnion R
    P ⊆ U ∧ Q ⊆ U ∧ E ⊆ U ∧ U = P ∪ Q ∪ E ∧
    (∀ i j : Fin 4, i ≠ j → Disjoint (F i) (F j)) ∧
    (∀ i, Disjoint (F i) E) ∧
    (∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x)) ∧
    (∀ i, ∀ a ∈ F i, ∀ b ∈ E, ¬ G.Adj a b) := by
  classical
  dsimp only
  have hPU : P ⊆ U := by
    rcases hP with rfl | ⟨i,hi,rfl⟩
    · exact Finset.empty_subset _
    · exact hsub i (Finset.mem_sdiff.mp hi).1
  have hQU : Q ⊆ U := by
    rcases hQ with rfl | ⟨i,hi,rfl⟩
    · exact Finset.empty_subset _
    · exact hsub i (Finset.mem_sdiff.mp hi).1
  have hEU : J.biUnion R ⊆ U := by
    intro v hv
    obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
    exact hsub i (hJK hi) hv
  have hUeq : U = P ∪ Q ∪ J.biUnion R := by
    ext v
    constructor
    · intro hv
      rw [←hcover] at hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      by_cases hij : i ∈ J
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hij,hv⟩)
      · have hi' : i ∈ K \ J := Finset.mem_sdiff.mpr ⟨hi,hij⟩
        rcases hslot i hi' with hp | hq
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hp ▸ hv))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hq ▸ hv))
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact hPU hv
        · exact hQU hv
      · exact hEU hv
  have hPE : Disjoint P (J.biUnion R) := by
    rcases hP with rfl | ⟨i,hi,rfl⟩
    · simp
    · apply Finset.disjoint_left.mpr
      intro v hv he
      obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp he
      have hij : i ≠ j := by intro h; subst j; exact (Finset.mem_sdiff.mp hi).2 hj
      exact Finset.disjoint_left.mp (hdis i (Finset.mem_sdiff.mp hi).1 j (hJK hj) hij) hv hvj
  have hQE : Disjoint Q (J.biUnion R) := by
    rcases hQ with rfl | ⟨i,hi,rfl⟩
    · simp
    · apply Finset.disjoint_left.mpr
      intro v hv he
      obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp he
      have hij : i ≠ j := by intro h; subst j; exact (Finset.mem_sdiff.mp hi).2 hj
      exact Finset.disjoint_left.mp (hdis i (Finset.mem_sdiff.mp hi).1 j (hJK hj) hij) hv hvj
  have hPQanti : ∀ a ∈ P, ∀ b ∈ Q, ¬ G.Adj a b := by
    rcases hP with rfl | ⟨i,hi,rfl⟩
    · simp
    · rcases hQ with rfl | ⟨j,hj,rfl⟩
      · simp
      · have hij : i ≠ j := by
          intro he; subst j
          obtain ⟨v,hv⟩ := hne i (Finset.mem_sdiff.mp hi).1
          exact Finset.disjoint_left.mp hPQ hv hv
        exact hanti i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hij
  have hPEanti : ∀ a ∈ P, ∀ b ∈ J.biUnion R, ¬ G.Adj a b := by
    rcases hP with rfl | ⟨i,hi,rfl⟩
    · simp
    · intro a ha b hb
      obtain ⟨j,hj,hb⟩ := Finset.mem_biUnion.mp hb
      have hij : i ≠ j := by intro he; subst j; exact (Finset.mem_sdiff.mp hi).2 hj
      exact hanti i (Finset.mem_sdiff.mp hi).1 j (hJK hj) hij a ha b hb
  have hQEanti : ∀ a ∈ Q, ∀ b ∈ J.biUnion R, ¬ G.Adj a b := by
    rcases hQ with rfl | ⟨i,hi,rfl⟩
    · simp
    · intro a ha b hb
      obtain ⟨j,hj,hb⟩ := Finset.mem_biUnion.mp hb
      have hij : i ≠ j := by intro he; subst j; exact (Finset.mem_sdiff.mp hi).2 hj
      exact hanti i (Finset.mem_sdiff.mp hi).1 j (hJK hj) hij a ha b hb
  have hXP : Disjoint X P := Finset.disjoint_of_subset_right hPU hXU
  have hXQ : Disjoint X Q := Finset.disjoint_of_subset_right hQU hXU
  have hYP : Disjoint Y P := Finset.disjoint_of_subset_right hPU hYU
  have hYQ : Disjoint Y Q := Finset.disjoint_of_subset_right hQU hYU
  have hXE : Disjoint X (J.biUnion R) := Finset.disjoint_of_subset_right hEU hXU
  have hYE : Disjoint Y (J.biUnion R) := Finset.disjoint_of_subset_right hEU hYU
  refine ⟨hPU,hQU,hEU,hUeq,?_,?_,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first | exact hXY | exact hXY.symm | exact hXP | exact hXP.symm | exact hXQ | exact hXQ.symm |
        exact hYP | exact hYP.symm | exact hYQ | exact hYQ.symm | exact hPQ | exact hPQ.symm
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] <;>
      first | exact hXE | exact hYE | exact hPE | exact hQE
  · intro i j hij a ha b hb hab
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> simp at ha hb <;>
      first | exact hcross a ha b hb hab
            | exact ⟨(hcross b hb a ha hab.symm).2,(hcross b hb a ha hab.symm).1⟩
            | exact False.elim (hXanti a ha b (hPU hb) hab)
            | exact False.elim (hXanti a ha b (hQU hb) hab)
            | exact False.elim (hXanti b hb a (hPU ha) hab.symm)
            | exact False.elim (hXanti b hb a (hQU ha) hab.symm)
            | exact False.elim (hYanti a ha b (hPU hb) hab)
            | exact False.elim (hYanti a ha b (hQU hb) hab)
            | exact False.elim (hYanti b hb a (hPU ha) hab.symm)
            | exact False.elim (hYanti b hb a (hQU ha) hab.symm)
            | exact False.elim (hPQanti a ha b hb hab)
            | exact False.elim (hPQanti b hb a ha hab.symm)
  · intro i a ha b hb
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at ha <;>
      first | exact hXanti a ha b (hEU hb) | exact hYanti a ha b (hEU hb) |
        exact hPEanti a ha b hb | exact hQEanti a ha b hb
