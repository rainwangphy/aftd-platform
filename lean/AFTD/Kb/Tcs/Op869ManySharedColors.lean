import AFTD.Prelude
import AFTD.Kb.Tcs.Op869DoubleCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op869_many_shared_colors

Topic: online_algorithms   Node: 5fd59351eda2

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.2 (the case i = 2)

If |B| < |A| and every element of A meets at least d elements of B, then at least d elements of B lie in at least two of the sets.
-/

theorem op869_many_shared_colors {α β : Type} [DecidableEq β]
    (A : Finset α) (B : Finset β) (E : α → Finset β) (d : ℕ)
    (hE : ∀ x ∈ A, E x ⊆ B) (hd : ∀ x ∈ A, d ≤ (E x).card) (hab : B.card < A.card) :
    d ≤ (B.filter (fun u => 2 ≤ (A.filter (fun x => u ∈ E x)).card)).card := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · omega
  have hA2 : 2 ≤ A.card := by
    obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    have h1 : 1 ≤ (E x).card := le_trans hd0 (hd x hx)
    have h2 := Finset.card_le_card (hE x hx)
    omega
  have h := op869_double_count A B E d 2 hE hd hA2
  set b2 := (B.filter (fun u => 2 ≤ (A.filter (fun x => u ∈ E x)).card)).card
  by_contra hlt
  push Not at hlt
  obtain ⟨a', ha'⟩ : ∃ a', A.card = a' + 2 := ⟨A.card - 2, by omega⟩
  obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [ha', hd'] at h
  rw [hd'] at hlt
  simp only [Nat.add_sub_cancel] at h
  have h3 : (a' + 1) * b2 ≤ (a' + 1) * d' := Nat.mul_le_mul_left _ (by omega)
  nlinarith
