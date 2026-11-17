import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# orderedFactorization_equiv_sigma

Topic: combinatorics   Node: e706b43209a0

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): helper for the recursion of H(m) (Section 3)

For n > 1, the ordered factorizations of n (lists of integers > 1 with product n) are in bijection with pairs (d, t) of a proper divisor d of n and an ordered factorization t of d, via l ↦ (product of the tail, tail) and (d, t) ↦ (n/d) :: t.
-/

theorem orderedFactorization_equiv_sigma (n : ℕ) (hn : 1 < n) :
    Nonempty ({l : List ℕ // (∀ a ∈ l, 1 < a) ∧ l.prod = n} ≃
      Σ d : n.properDivisors, {t : List ℕ // (∀ a ∈ t, 1 < a) ∧ t.prod = d.1}) := by
  have hpos : ∀ l : List ℕ, (∀ a ∈ l, 1 < a) → 0 < l.prod := fun l hl =>
    List.prod_pos (fun a ha => by have := hl a ha; omega)
  have tail_mem : ∀ l : List ℕ, (∀ a ∈ l, 1 < a) → l.prod = n → l.tail.prod ∈ n.properDivisors := by
    intro l h1 h2
    cases l with
    | nil => simp at h2; omega
    | cons a t =>
      have ha := h1 a (by simp)
      have ht := hpos t (fun b hb => h1 b (by simp [hb]))
      simp only [List.prod_cons] at h2
      simp only [List.tail_cons, Nat.mem_properDivisors]
      refine ⟨⟨a, by rw [← h2, mul_comm]⟩, ?_⟩
      rw [← h2]
      nlinarith
  have tail_ok : ∀ l : List ℕ, (∀ a ∈ l, 1 < a) → ∀ a ∈ l.tail, 1 < a :=
    fun l h1 a ha => h1 a (List.mem_of_mem_tail ha)
  have head_ok : ∀ d ∈ n.properDivisors, 1 < n / d := by
    intro d hd
    obtain ⟨⟨k, hk⟩, hlt⟩ := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hk; omega
      · exact h
    rw [hk, Nat.mul_div_cancel_left k hd0]
    rw [hk] at hlt
    have : d * 1 < d * k := by simpa using hlt
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨
    { toFun := fun l => ⟨⟨l.1.tail.prod, tail_mem l.1 l.2.1 l.2.2⟩, ⟨l.1.tail, tail_ok l.1 l.2.1, rfl⟩⟩
      invFun := fun s => ⟨(n / s.1.1) :: s.2.1, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact head_ok _ s.1.2
    · exact s.2.2.1 a ha
  · rw [List.prod_cons, s.2.2.2]
    exact Nat.div_mul_cancel (Nat.mem_properDivisors.mp s.1.2).1
  · rintro ⟨l, h1, h2⟩
    cases l with
    | nil => simp at h2; omega
    | cons a t =>
      apply Subtype.ext
      simp only [List.tail_cons, List.cons.injEq, and_true]
      have ht := hpos t (fun b hb => h1 b (by simp [hb]))
      rw [← h2, List.prod_cons, Nat.mul_div_cancel _ ht]
  · rintro ⟨⟨d, hd⟩, t, ht1, ht2⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      simp [ht2]
    · rfl
