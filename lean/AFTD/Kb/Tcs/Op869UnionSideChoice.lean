import AFTD.Prelude

/-!
# op869_union_side_choice

Topic: online_algorithms   Node: acb40bbbb716

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.1

For finite sets P, Q, X with |P|, |Q| at least a, |X| = t and X disjoint from P, one of P ∪ Q and Q ∪ X has at least a + ⌈t/2⌉ elements.
-/

theorem op869_union_side_choice {α : Type} [DecidableEq α] (P Q X : Finset α) (a t : ℕ)
    (hP : a ≤ P.card) (hQ : a ≤ Q.card) (hX : X.card = t) (hXP : Disjoint X P) :
    a + (t + 1) / 2 ≤ max (P ∪ Q).card (Q ∪ X).card := by
  by_contra hcon
  push Not at hcon
  have h1 : (P ∪ Q).card < a + (t + 1) / 2 := lt_of_le_of_lt (le_max_left _ _) hcon
  have h2 : (Q ∪ X).card < a + (t + 1) / 2 := lt_of_le_of_lt (le_max_right _ _) hcon
  have hsd : (P ∪ Q).card = P.card + (Q \ P).card := by
    rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
  have hsub : X ∩ Q ⊆ Q \ P := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_sdiff]
    exact ⟨hx.2, Finset.disjoint_left.mp hXP hx.1⟩
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_add_card_inter Q X
  rw [Finset.inter_comm] at hu
  omega
