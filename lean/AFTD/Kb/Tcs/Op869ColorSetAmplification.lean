import AFTD.Prelude
import AFTD.Kb.Tcs.Op869UnionSideChoice

/-!
# op869_color_set_amplification

Topic: online_algorithms   Node: a0e60205402f

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.1; a combinatorial step toward the three-colorable adversary construction.

If P and Q each have at least a elements and X has t elements disjoint from P, then P union Q or Q union X has at least a plus ceil(t/2) elements.
-/

theorem op869_color_set_amplification {α : Type} [DecidableEq α] (P Q X : Finset α) (a t : ℕ) :
    a ≤ P.card → a ≤ Q.card → X.card = t → Disjoint X P →
    a + (t + 1) / 2 ≤ (P ∪ Q).card ∨ a + (t + 1) / 2 ≤ (Q ∪ X).card := by
  intro hP hQ hX hd
  have h := op869_union_side_choice P Q X a t hP hQ hX hd
  rcases le_total (P ∪ Q).card (Q ∪ X).card with hle | hle
  · right
    simpa [max_eq_right hle] using h
  · left
    simpa [max_eq_left hle] using h
