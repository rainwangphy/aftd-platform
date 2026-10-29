import AFTD.Prelude
import AFTD.Kb.Tcs.ExistsMemCardFilterSubsetLeMul
import AFTD.Kb.Tcs.CardFilterSubsetLeOneOfCardEq

/-!
# intersecting_uniform_hypergraph_card_le_pow

Topic: combinatorics   Node: 997b726966c2

Provenance: formalization of a published result. Source: arXiv:2610.37315 Theorem 1.1 -- The maximum size of intersecting k-graphs with covering number k

Let α be a type with decidable equality and let k ≥ 1 be a natural number. Let ℱ be a finite family of finite subsets of α such that every F ∈ ℱ has cardinality k. Suppose that for all F1, F2 ∈ ℱ, the intersection F1 ∩ F2 is nonempty, and that for every finite subset A of α with cardinality less than k, there exists F ∈ ℱ such that A and F are disjoint. Then the cardinality of ℱ is at most k^k.
-/

/-- The size of an intersecting k-uniform hypergraph with covering number k is at most k^k. -/
theorem intersecting_uniform_hypergraph_card_le_pow {α : Type*} [DecidableEq α]
    (k : ℕ) (hk : 1 ≤ k) (ℱ : Finset (Finset α))
    (hunif : ∀ F ∈ ℱ, F.card = k)
    (hinter : ∀ F1 ∈ ℱ, ∀ F2 ∈ ℱ, (F1 ∩ F2).Nonempty)
    (htau : ∀ (A : Finset α), A.card < k → ∃ F ∈ ℱ, Disjoint A F) :
    ℱ.card ≤ k ^ k := by
  have hind : ∀ m ≤ k, ∀ (A : Finset α), A.card = k - m → (ℱ.filter (fun F => A ⊆ F)).card ≤ k ^ m := by
    intro m
    induction m with
    | zero =>
      intro _ A hA
      have hAk : A.card = k := by omega
      have hle1 := card_filter_subset_le_one_of_card_eq k ℱ hunif A hAk
      simp only [pow_zero]
      exact hle1
    | succ m ih =>
      intro hmk A hA
      have hlt : A.card < k := by omega
      obtain ⟨F, hF, hdisj⟩ := htau A hlt
      have hFcard : F.card = k := hunif F hF
      obtain ⟨x, hxF, hle⟩ := exists_mem_card_filter_subset_le_mul k hk ℱ A F hinter hF hFcard
      have hxnot : x ∉ A := fun hxA => Finset.disjoint_left.mp hdisj hxA hxF
      have hcard_succ : (insert x A).card = k - m := by
        rw [Finset.card_insert_of_notMem hxnot, hA]
        omega
      have hmk' : m ≤ k := by omega
      have hih := ih hmk' (insert x A) hcard_succ
      calc (ℱ.filter (fun F => A ⊆ F)).card
        _ ≤ k * (ℱ.filter (fun F => insert x A ⊆ F)).card := hle
        _ ≤ k * k ^ m := Nat.mul_le_mul_left k hih
        _ = k ^ (m + 1) := by ring
  have h0 : (∅ : Finset α).card = k - k := by simp
  have h_filter : (ℱ.filter (fun F => (∅ : Finset α) ⊆ F)) = ℱ := by
    ext F
    simp
  have h_final := hind k le_rfl ∅ h0
  rw [h_filter] at h_final
  exact h_final
