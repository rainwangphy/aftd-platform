import AFTD.Prelude
import AFTD.Kb.Tcs.Op869DoubleCount

/-!
# op869_incidence_degree_count

Topic: online_algorithms   Node: 7198626feb8a

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.2; double-counting step toward the three-colorable adversary construction.

For a finite incidence relation in which each element of A is incident with at least d elements of B, and 1 ≤ r ≤ |A|, the incidence count |A|d is at most |B|(r−1) plus (|A|−(r−1)) times the number of elements of B incident with at least r elements of A.
-/

theorem op869_incidence_degree_count {α β : Type} [DecidableEq α] [DecidableEq β] (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [DecidableRel R] (d r : ℕ) :
    1 ≤ r → r ≤ A.card → (∀ a ∈ A, d ≤ (B.filter (R a)).card) →
    A.card * d ≤ B.card * (r - 1) +
      (A.card - (r - 1)) * (B.filter (fun b => r ≤ (A.filter (fun a => R a b)).card)).card := by
  intro hr hrA hd
  let E : α → Finset β := fun a => B.filter (R a)
  have hE : ∀ a ∈ A, E a ⊆ B := by
    intro a ha b hb
    exact (Finset.mem_filter.mp hb).1
  have hcard : (B.filter (fun b => r ≤ (A.filter (fun a => b ∈ E a)).card)) =
      B.filter (fun b => r ≤ (A.filter (fun a => R a b)).card) := by
    apply Finset.filter_congr
    intro b hb
    have heq : (A.filter (fun a => b ∈ E a)) = A.filter (fun a => R a b) := by
      ext a
      simp [E, hb]
    rw [heq]
  have h := op869_double_count A B E d r hE hd hrA
  rw [hcard] at h
  have harith : A.card - r + 1 = A.card - (r - 1) := by omega
  rwa [harith] at h
