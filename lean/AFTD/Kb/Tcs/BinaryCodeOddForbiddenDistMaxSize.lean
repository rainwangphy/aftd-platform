import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryCodeParityClassAvoidsOddDist
import AFTD.Kb.Tcs.BinaryCodeParityClassCard
import AFTD.Kb.Tcs.BinaryCodeAvoidsOddDistCardLe

/-!
# binary_code_odd_forbidden_dist_max_size

Topic: combinatorics   Node: f30a316f84e8

Provenance: formalization of a published result. Source: arXiv:2611.04523, Proposition 3.1

Let n ≥ 1 and 1 ≤ d ≤ n be integers such that d is odd. Then every subset F : Finset (Fin n → Fin 2) such that no two elements of F have Hamming distance d satisfies F.card ≤ 2 ^ (n - 1), and there exists a subset F : Finset (Fin n → Fin 2) with no two elements having Hamming distance d whose cardinality is 2 ^ (n - 1).
-/

/-- The maximum cardinality of a binary code in {0,1}^n avoiding an odd Hamming distance d is 2^(n-1). -/
theorem binary_code_odd_forbidden_dist_max_size (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) (hodd : Odd d) : (∀ F : Finset (Fin n → Fin 2), (∀ x ∈ F, ∀ y ∈ F, hammingDist x y ≠ d) → F.card ≤ 2 ^ (n - 1)) ∧ ∃ F : Finset (Fin n → Fin 2), (∀ x ∈ F, ∀ y ∈ F, hammingDist x y ≠ d) ∧ F.card = 2 ^ (n - 1) := by
  refine ⟨fun F hF => binary_code_avoids_odd_dist_card_le n d hn hd hdn F hF, ?_⟩
  refine ⟨Finset.univ.filter (fun x : Fin n → Fin 2 => (∑ i, x i) = 0), ?_, ?_⟩
  · intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    exact binary_code_parity_class_avoids_odd_dist n d hodd 0 x y hx.2 hy.2
  · exact binary_code_parity_class_card n hn 0
