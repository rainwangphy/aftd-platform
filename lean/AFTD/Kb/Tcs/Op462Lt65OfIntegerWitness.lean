import AFTD.Prelude
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.GaleDistanceGraph
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.Op462MinCardLeOfIntegerWitness

/-!
# op462_lt65_of_integer_witness

Topic: combinatorics   Node: 89b1c66f7100

Provenance: helper lemma. step towards op_462_min_gale_counterexample_card_three_lt_sixty_five

An integer coordinate certificate on fewer than 65 indexed points, with unit diameter bound, a strict threshold gap, and a non-four-colorable edge graph, implies min_gale_counterexample_card_three < 65.
-/

/-- An integer coordinate certificate on fewer than 65 indexed points, with unit diameter bound, a strict threshold gap, and a non-four-colorable edge graph, implies min_gale_counterexample_card_three < 65. -/
theorem op462_lt65_of_integer_witness (n : ℕ) (hn : n < 65) (S Q : ℤ) (hS : 0 < S) (P : Fin n → Fin 3 → ℤ) (E : List (Fin n × Fin n)) (hunit : ∀ i j, (∑ k : Fin 3, (P i k - P j k)^2) ≤ S^2) (hedge : E.all (fun e => decide (Q ≤ ∑ k : Fin 3, (P e.1 k - P e.2 k)^2)) = true) (hgap : gale_sigma_three^2 < (Q : ℝ) / (S : ℝ)^2) (hnotcolor : ∀ c : Fin n → Fin 4, (∀ e ∈ E, c e.1 ≠ c e.2) → False) (a b : Fin n) (hab : (a,b) ∈ E) : min_gale_counterexample_card_three < 65 := lt_of_le_of_lt (op_462_min_card_le_of_integer_witness n S Q hS P E hunit hedge hgap hnotcolor a b hab) hn
