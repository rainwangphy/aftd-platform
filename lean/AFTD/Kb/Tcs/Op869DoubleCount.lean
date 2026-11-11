import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_double_count

Topic: online_algorithms   Node: b77b0a8fe7f4

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.2

Double counting in a bipartite incidence: if every element x of A meets at least d elements of B, then for i ≤ |A|, |A|·d ≤ |B|·(i-1) + (|A|-i+1)·(number of elements of B lying in at least i of the sets).
-/

theorem op869_double_count {α β : Type} [DecidableEq β]
    (A : Finset α) (B : Finset β) (E : α → Finset β) (d i : ℕ)
    (hE : ∀ x ∈ A, E x ⊆ B) (hd : ∀ x ∈ A, d ≤ (E x).card) (hi : i ≤ A.card) :
    A.card * d ≤ B.card * (i - 1) +
      (A.card - i + 1) * (B.filter (fun u => i ≤ (A.filter (fun x => u ∈ E x)).card)).card := by
  classical
  set deg : β → ℕ := fun u => (A.filter (fun x => u ∈ E x)).card with hdeg
  have hsum : ∑ x ∈ A, (E x).card = ∑ u ∈ B, deg u := by
    have h1 : ∀ x ∈ A, (E x).card = ∑ u ∈ B, if u ∈ E x then 1 else 0 := by
      intro x hx
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext u; simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hE x hx h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_boole, Nat.cast_id]
  have hlow : A.card * d ≤ ∑ x ∈ A, (E x).card := by
    calc A.card * d = ∑ _x ∈ A, d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hd
  have hdegle : ∀ u, deg u ≤ A.card := fun u => Finset.card_filter_le _ _
  set H := B.filter (fun u => i ≤ deg u) with hH
  have hsplit := Finset.sum_filter_add_sum_filter_not B (fun u => i ≤ deg u) deg
  have hhigh : ∑ u ∈ B.filter (fun u => i ≤ deg u), deg u ≤ H.card * A.card := by
    calc _ ≤ ∑ _u ∈ H, A.card := Finset.sum_le_sum fun u _ => hdegle u
      _ = H.card * A.card := by rw [Finset.sum_const, smul_eq_mul]
  have hlo : ∑ u ∈ B.filter (fun u => ¬ i ≤ deg u), deg u ≤
      (B.filter (fun u => ¬ i ≤ deg u)).card * (i - 1) := by
    calc _ ≤ ∑ _u ∈ B.filter (fun u => ¬ i ≤ deg u), (i - 1) :=
          Finset.sum_le_sum fun u hu => by
            have := (Finset.mem_filter.mp hu).2
            omega
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hcardsplit : H.card + (B.filter (fun u => ¬ i ≤ deg u)).card = B.card :=
    Finset.card_filter_add_card_filter_not _
  have key : A.card * d ≤ H.card * A.card + (B.filter (fun u => ¬ i ≤ deg u)).card * (i - 1) := by
    omega
  -- H.card * A.card + (B - H) * (i-1) = B*(i-1) + H*(A - (i-1))
  have hHle : H.card ≤ B.card := Finset.card_filter_le _ _
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp only [Nat.zero_sub, mul_zero, zero_add, Nat.sub_zero] at key ⊢
    calc A.card * d ≤ H.card * A.card := by simpa using key
      _ ≤ (A.card + 1) * H.card := by nlinarith
  · have hrw : A.card - i + 1 = A.card - (i - 1) := by omega
    rw [hrw]
    have hBH : (B.filter (fun u => ¬ i ≤ deg u)).card = B.card - H.card := by omega
    rw [hBH] at key
    have e1 : (B.card - H.card) * (i - 1) + H.card * (i - 1) = B.card * (i - 1) := by
      rw [← add_mul, Nat.sub_add_cancel hHle]
    have e2 : (A.card - (i - 1)) * H.card + (i - 1) * H.card = A.card * H.card := by
      rw [← add_mul, Nat.sub_add_cancel (by omega)]
    nlinarith [e1, e2]
