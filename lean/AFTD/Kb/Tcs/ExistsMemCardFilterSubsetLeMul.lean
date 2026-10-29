import AFTD.Prelude
import AFTD.Kb.Tcs.ExistsLeMulOfLeSum
import AFTD.Kb.Tcs.CardFilterSubsetLeSumCardFilterInsert

/-!
# exists_mem_card_filter_subset_le_mul

Topic: combinatorics   Node: 5309c94a8324

Provenance: helper lemma. arXiv:2610.37315 Claim 1.2

Let α be a type with decidable equality, let k ≥ 1 be a natural number, and let ℱ be a finite family of finite subsets of α such that for all F1, F2 ∈ ℱ, the intersection F1 ∩ F2 is nonempty. For any finite subset A of α and any F ∈ ℱ with cardinality k, there exists x ∈ F such that the number of sets in ℱ containing A is at most k times the number of sets in ℱ containing insert x A.
-/

/-- In an intersecting family, for any set A and edge F of size k, some x ∈ F satisfies |ℱ(A)| ≤ k * |ℱ(A ∪ {x})|. -/
lemma exists_mem_card_filter_subset_le_mul {α : Type*} [DecidableEq α]
    (k : ℕ) (hk : 1 ≤ k) (ℱ : Finset (Finset α)) (A F : Finset α)
    (hinter : ∀ F1 ∈ ℱ, ∀ F2 ∈ ℱ, (F1 ∩ F2).Nonempty)
    (hF : F ∈ ℱ) (hcard : F.card = k) :
    ∃ x ∈ F, (ℱ.filter (fun F' => A ⊆ F')).card ≤
      k * (ℱ.filter (fun F' => insert x A ⊆ F')).card := by
  have hsum := card_filter_subset_le_sum_card_filter_insert ℱ A F hinter hF
  exact exists_le_mul_of_le_sum F (fun x => (ℱ.filter (fun F' => insert x A ⊆ F')).card) k hk hcard _ hsum
