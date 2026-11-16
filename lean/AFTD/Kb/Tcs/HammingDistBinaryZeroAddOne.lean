import AFTD.Prelude

/-!
# hamming_dist_binary_zero_add_one

Topic: information   Node: 48062cf3e7a6

Provenance: helper lemma. arXiv:2611.18156 Equation (16)

For any binary vector x : Fin n → Fin 2 of length n, the Hamming distance from the all-zeros vector to x plus the Hamming distance from the all-ones vector to x equals n.
-/

/-- For any binary word x of length n, the sum of its Hamming distances to the all-zeros word and to the all-ones word is n. -/
lemma hamming_dist_binary_zero_add_one (n : ℕ) (x : Fin n → Fin 2) :
    hammingDist (fun _ : Fin n => (0 : Fin 2)) x + hammingDist (fun _ : Fin n => (1 : Fin 2)) x = n := by
  have h (i : Fin n) : ((1 : Fin 2) ≠ x i) ↔ ¬ ((0 : Fin 2) ≠ x i) := by
    generalize x i = a
    fin_cases a <;> decide
  have h1 : Finset.filter (fun i => (1 : Fin 2) ≠ x i) Finset.univ =
      Finset.filter (fun i => ¬ ((0 : Fin 2) ≠ x i)) Finset.univ :=
    Finset.filter_congr fun i _ => h i
  unfold hammingDist
  rw [h1, Finset.card_filter_add_card_filter_not]
  exact Fintype.card_fin n
