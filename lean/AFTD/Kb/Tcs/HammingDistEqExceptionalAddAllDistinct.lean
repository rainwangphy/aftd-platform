import AFTD.Prelude
import AFTD.Kb.Tcs.HammingExceptionalCoords
import AFTD.Kb.Tcs.HammingAllDistinctCoords

/-!
# hamming_dist_eq_exceptional_add_all_distinct

Topic: combinatorics   Node: cea5ff8c514f

Provenance: helper lemma. arXiv:2610.32789 "Triangle-Free Sets in Exact-Distance Hamming Graphs", Proposition 2.2

For vectors $x, y, z : \mathrm{Fin}\, n \to \alpha$, the Hamming distance $\mathrm{hammingDist}(x, y)$ equals the number of coordinates where $x$ is exceptional, plus the number where $y$ is exceptional, plus the number where all three coordinates are distinct.
-/

/-- The Hamming distance between x and y is the sum of exceptional coordinates for x, exceptional coordinates for y, and all-distinct coordinates. -/
theorem hamming_dist_eq_exceptional_add_all_distinct {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    hammingDist x y =
      (hamming_exceptional_coords x y z).card +
      (hamming_exceptional_coords y x z).card +
      (hamming_all_distinct_coords x y z).card := by
  have prop_equiv (a b c : α) :
      (a ≠ b) ↔ ((b = c ∧ a ≠ b) ∨ (a = c ∧ b ≠ a)) ∨ (a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
    tauto
  have h_split : (Finset.filter (fun i => x i ≠ y i) (Finset.univ : Finset (Fin n))) =
      (hamming_exceptional_coords x y z ∪ hamming_exceptional_coords y x z) ∪
      hamming_all_distinct_coords x y z := by
    have h_congr : (Finset.filter (fun i => x i ≠ y i) (Finset.univ : Finset (Fin n))) =
        Finset.filter (fun i => ((y i = z i ∧ x i ≠ y i) ∨ (x i = z i ∧ y i ≠ x i)) ∨
          (x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i)) Finset.univ :=
      Finset.filter_congr (fun i _ => prop_equiv (x i) (y i) (z i))
    rw [h_congr, Finset.filter_or, Finset.filter_or]
    rfl
  have disj1 : Disjoint (hamming_exceptional_coords x y z) (hamming_exceptional_coords y x z) := by
    rw [hamming_exceptional_coords, hamming_exceptional_coords, Finset.disjoint_filter]
    intro i _ ⟨hyz, hxy⟩ ⟨hxz, _⟩
    apply hxy
    rw [hyz, hxz]
  have disj2 : Disjoint (hamming_exceptional_coords x y z ∪ hamming_exceptional_coords y x z)
      (hamming_all_distinct_coords x y z) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [hamming_exceptional_coords, hamming_all_distinct_coords, Finset.disjoint_filter]
      intro i _ ⟨hyz, _⟩ ⟨_, _, hyz'⟩
      exact hyz' hyz
    · rw [hamming_exceptional_coords, hamming_all_distinct_coords, Finset.disjoint_filter]
      intro i _ ⟨hxz, _⟩ ⟨_, hxz', _⟩
      exact hxz' hxz
  change (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = _
  rw [h_split, Finset.card_union_of_disjoint disj2, Finset.card_union_of_disjoint disj1]
