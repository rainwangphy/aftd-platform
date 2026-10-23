import AFTD.Prelude

/-!
# bipartite_cycle_length_le

Topic: graphs   Node: 891811f0a886

Provenance: helper lemma. folklore

In any bipartite graph with vertex parts V and W, every simple cycle has length at most 2 * min(|V|, |W|).
-/

lemma bipartite_cycle_length_le_side_ne {V W : Type*}
    (G : SimpleGraph (V ⊕ W)) (hG : G ≤ completeBipartiteGraph V W)
    {a c : V ⊕ W} (h : G.Adj a c) : a.isLeft ≠ c.isLeft := by
  have := hG h
  cases a <;> cases c <;> simp_all [completeBipartiteGraph]

lemma bipartite_cycle_length_le_bool_shift_sum (m : ℕ) (b : ℕ → Bool) :
    (∑ i ∈ Finset.range m, if b (i + 1) then 1 else 0) + (if b 0 then 1 else 0) =
    (∑ i ∈ Finset.range m, if b i then 1 else 0) + (if b m then 1 else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega

lemma bipartite_cycle_length_le_bool_sum_alt (n : ℕ) (b : ℕ → Bool) (halt : ∀ i < n, b i ≠ b (i + 1)) :
    (∑ i ∈ Finset.range n, if b i then 1 else 0) + (∑ i ∈ Finset.range n, if b (i + 1) then 1 else 0) = n := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ Finset.range n, (if b i then 1 else 0) + (if b (i + 1) then 1 else 0) = 1 := by
    intro i hi
    have hne := halt i (Finset.mem_range.mp hi)
    cases h1 : b i <;> cases h2 : b (i + 1)
    · rw [h1, h2] at hne; contradiction
    · simp
    · simp
    · rw [h1, h2] at hne; contradiction
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma bipartite_cycle_length_le_bool_sum (n : ℕ) (b : ℕ → Bool)
    (hcyc : b n = b 0) (halt : ∀ i < n, b i ≠ b (i + 1)) :
    n = 2 * ∑ i ∈ Finset.range n, if b i then 1 else 0 := by
  have h1 := bipartite_cycle_length_le_bool_shift_sum n b
  have h2 := bipartite_cycle_length_le_bool_sum_alt n b halt
  rw [hcyc] at h1
  omega

lemma bipartite_cycle_length_le_card_le_card_V {V W : Type*} [Fintype V] (T : Finset (V ⊕ W)) (hT : ∀ x ∈ T, x.isLeft = true) :
    T.card ≤ Fintype.card V := by
  classical
  have hsub : T ⊆ Finset.image Sum.inl (Finset.univ : Finset V) := by
    intro x hx
    have hx' := hT x hx
    cases x with
    | inl v =>
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    | inr w =>
      simp at hx'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ] at hcard
  exact hcard

lemma bipartite_cycle_length_le_card_le_card_W {V W : Type*} [Fintype W] (T : Finset (V ⊕ W)) (hT : ∀ x ∈ T, x.isRight = true) :
    T.card ≤ Fintype.card W := by
  classical
  have hsub : T ⊆ Finset.image Sum.inr (Finset.univ : Finset W) := by
    intro x hx
    have hx' := hT x hx
    cases x with
    | inl v =>
      simp at hx'
    | inr w =>
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ] at hcard
  exact hcard

lemma bipartite_cycle_length_le_isRight_eq_true_of_isLeft_eq_false {V W : Type*} (x : V ⊕ W) (h : x.isLeft = false) :
    x.isRight = true := by
  cases x with
  | inl _ => simp at h
  | inr _ => rfl

/-- Any simple cycle in a bipartite graph has length at most twice the size of the smaller shore. -/
theorem bipartite_cycle_length_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph (V ⊕ W)) (hG : G ≤ completeBipartiteGraph V W)
    {u : V ⊕ W} (p : G.Walk u u) (hp : p.IsCycle) :
    p.length ≤ 2 * min (Fintype.card V) (Fintype.card W) := by
  classical
  let b : ℕ → Bool := fun i => (p.getVert i).isLeft
  have halt : ∀ i < p.length, b i ≠ b (i + 1) := fun i hi =>
    bipartite_cycle_length_le_side_ne G hG (p.adj_getVert_succ hi)
  have hcyc : b p.length = b 0 := by
    simp [b, p.getVert_length, p.getVert_zero]
  have hlen : p.length = 2 * ∑ i ∈ Finset.range p.length, if b i then 1 else 0 :=
    bipartite_cycle_length_le_bool_sum p.length b hcyc halt
  let SF := (Finset.range p.length).filter (fun i => b i = true)
  let SG := (Finset.range p.length).filter (fun i => b i = false)
  have hSF_range : ∀ i ∈ SF, i < p.length := fun i hi => Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hSG_range : ∀ i ∈ SG, i < p.length := fun i hi => Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hinjV : Set.InjOn p.getVert ↑SF := by
    intro i hi j hj hij
    have hi' : i ≤ p.length - 1 := Nat.le_sub_one_of_lt (hSF_range i (Finset.mem_coe.mp hi))
    have hj' : j ≤ p.length - 1 := Nat.le_sub_one_of_lt (hSF_range j (Finset.mem_coe.mp hj))
    exact hp.getVert_injOn' hi' hj' hij
  have hinjW : Set.InjOn p.getVert ↑SG := by
    intro i hi j hj hij
    have hi' : i ≤ p.length - 1 := Nat.le_sub_one_of_lt (hSG_range i (Finset.mem_coe.mp hi))
    have hj' : j ≤ p.length - 1 := Nat.le_sub_one_of_lt (hSG_range j (Finset.mem_coe.mp hj))
    exact hp.getVert_injOn' hi' hj' hij
  have hSF_card : SF.card = ∑ i ∈ Finset.range p.length, if b i then 1 else 0 := by
    rw [Finset.card_filter]
  have hSG_card : SG.card = ∑ i ∈ Finset.range p.length, if ¬b i then 1 else 0 := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases b i <;> rfl
  have hV : (∑ i ∈ Finset.range p.length, if b i then 1 else 0) ≤ Fintype.card V := by
    rw [← hSF_card, ← Finset.card_image_of_injOn hinjV]
    apply bipartite_cycle_length_le_card_le_card_V
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  have hW : (∑ i ∈ Finset.range p.length, if b i then 1 else 0) ≤ Fintype.card W := by
    have hsum : (∑ i ∈ Finset.range p.length, if b i then 1 else 0) +
                (∑ i ∈ Finset.range p.length, if ¬b i then 1 else 0) = p.length := by
      rw [← Finset.sum_add_distrib]
      have : ∀ i ∈ Finset.range p.length, (if b i then 1 else 0) + (if ¬b i then 1 else 0) = 1 := by
        intro i _
        cases b i <;> rfl
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    have hSG_le : SG.card ≤ Fintype.card W := by
      rw [← Finset.card_image_of_injOn hinjW]
      apply bipartite_cycle_length_le_card_le_card_W
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact bipartite_cycle_length_le_isRight_eq_true_of_isLeft_eq_false (p.getVert i) ((Finset.mem_filter.mp hi).2)
    have : (∑ i ∈ Finset.range p.length, if b i then 1 else 0) =
           (∑ i ∈ Finset.range p.length, if ¬b i then 1 else 0) := by
      omega
    rw [this, ← hSG_card]
    exact hSG_le
  rw [hlen]
  have hmin : (∑ i ∈ Finset.range p.length, if b i then 1 else 0) ≤ min (Fintype.card V) (Fintype.card W) :=
    le_min hV hW
  exact Nat.mul_le_mul_left 2 hmin
