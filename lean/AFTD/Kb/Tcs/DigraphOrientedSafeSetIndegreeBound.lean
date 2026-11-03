import AFTD.Prelude

/-!
# digraph_oriented_safe_set_indegree_bound

Topic: graphs   Node: 2fa16f7fcec5

Provenance: helper lemma. Boundary counting for the safe-cycle obstruction in OP-110; experiment 13260.

In a finite loopless oriented digraph of minimum indegree r, a set to which each outside vertex sends at most two arcs satisfies r times its size at most its number of unordered internal pairs plus twice the outside size.
-/

theorem digraph_oriented_safe_set_indegree_bound
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (r : ℕ) (hin : ∀ v, r ≤ (Finset.univ.filter fun u => D.Adj u v).card)
    (C : Finset α)
    (hsafe : ∀ v ∉ C, (C.filter fun w => D.Adj v w).card ≤ 2) :
    r * C.card ≤ Nat.choose C.card 2 + 2 * (Fintype.card α - C.card) := by
  classical
  let A := (C.product C).filter fun p => D.Adj p.1 p.2
  let U := (Finset.univ : Finset α) \ C
  let edge : α × α → Sym2 α := fun p => s(p.1,p.2)
  have hinj : Set.InjOn edge (↑A : Set (α × α)) := by
    rintro ⟨a,b⟩ ha ⟨c,d⟩ hb he
    have hab : D.Adj a b := (Finset.mem_filter.mp ha).2
    have hcd : D.Adj c d := (Finset.mem_filter.mp hb).2
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext h.1 h.2
    · change a = d ∧ b = c at h
      have hba : D.Adj b a := by rw [h.1,h.2]; exact hcd
      exact (hori a b hab hba).elim
  have hsub : A.image edge ⊆ C.offDiag.image Sym2.mk.uncurry := by
    intro e he
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp he
    have hp := (Finset.mem_filter.mp hab).1
    have ha : a ∈ C := (Finset.mem_product.mp hp).1
    have hb : b ∈ C := (Finset.mem_product.mp hp).2
    have hab' : D.Adj a b := (Finset.mem_filter.mp hab).2
    have hne : a ≠ b := by intro h; subst b; exact hloop a hab'
    apply Finset.mem_image.mpr
    exact ⟨(a,b), Finset.mem_offDiag.mpr ⟨ha,hb,hne⟩, rfl⟩
  have hA : A.card ≤ Nat.choose C.card 2 := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj, Sym2.card_image_offDiag] at hc
    exact hc
  have hAcount : A.card = ∑ u ∈ C, (C.filter fun v => D.Adj u v).card := by
    simp only [A, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_product C C (fun p => if D.Adj p.1 p.2 then 1 else 0)
  have hsumint : (∑ v ∈ C, (C.filter fun u => D.Adj u v).card) = A.card := by
    rw [hAcount]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsumext : (∑ v ∈ C, (U.filter fun u => D.Adj u v).card) =
      ∑ u ∈ U, (C.filter fun v => D.Adj u v).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsplit (v : α) :
      (C.filter fun u => D.Adj u v).card + (U.filter fun u => D.Adj u v).card =
        (Finset.univ.filter fun u => D.Adj u v).card := by
    have hd : Disjoint (C.filter fun u => D.Adj u v) (U.filter fun u => D.Adj u v) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1
    rw [← Finset.card_union_of_disjoint hd]
    congr 1
    ext x
    by_cases hx : x ∈ C <;> simp [U, hx]
  have htotal : r * C.card ≤ A.card + ∑ u ∈ U, (C.filter fun v => D.Adj u v).card := by
    calc
      r * C.card = ∑ _v ∈ C, r := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ C, (Finset.univ.filter fun u => D.Adj u v).card := by
        exact Finset.sum_le_sum fun v _ => hin v
      _ = (∑ v ∈ C, (C.filter fun u => D.Adj u v).card) +
          (∑ v ∈ C, (U.filter fun u => D.Adj u v).card) := by
        simp_rw [← hsplit]
        rw [Finset.sum_add_distrib]
      _ = _ := by rw [hsumint, hsumext]
  have hU : U.card = Fintype.card α - C.card := by
    simp [U, Finset.card_sdiff]
  have hexternal : (∑ u ∈ U, (C.filter fun v => D.Adj u v).card) ≤ 2 * U.card := by
    calc
      _ ≤ ∑ _u ∈ U, 2 := by
        apply Finset.sum_le_sum
        intro u hu
        exact hsafe u (Finset.mem_sdiff.mp hu).2
      _ = _ := by simp [Nat.mul_comm]
  rw [hU] at hexternal
  omega
