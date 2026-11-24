import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeOutcome

/-!
# is_admissible_lottery

Topic: social_choice   Node: 085c9ceb0eb5

Provenance: formalization of a published result. Source: arXiv:2610.24217, Section 2.2 and Section 4.2

For n parties with vote shares p : Fin n → ℝ and house size h, a function dist : Finset (Fin n) → ℝ is an admissible lottery if dist is non-negative everywhere, is supported on subsets of size k = h - ∑ i, Nat.floor (h * p i) (i.e. dist S ≠ 0 implies S.card = k), sums to 1 over subsets of size k, satisfies is_envy_free_outcome p h S for every subset S with dist S ≠ 0, and has expected seat count ∑ S ∈ Finset.powersetCard k Finset.univ, dist S * (Nat.floor (h * p i) + (if i ∈ S then 1 else 0)) equal to h * p i for every party i.
-/

open Classical in
/-- A lottery on extra-seat subsets is admissible if it is non-negative, supported on size-k subsets, sums to 1, has envy-free support, and matches expected seats. -/
def is_admissible_lottery {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (dist : Finset (Fin n) → ℝ) : Prop :=
  let l (i : Fin n) := Nat.floor (h * p i)
  let k := h - ∑ i, l i
  (∀ S, 0 ≤ dist S) ∧
  (∀ S, dist S ≠ 0 → S.card = k) ∧
  (∑ S ∈ Finset.powersetCard k Finset.univ, dist S = 1) ∧
  (∀ S, dist S ≠ 0 → is_envy_free_outcome p h S) ∧
  (∀ i : Fin n, ∑ S ∈ Finset.powersetCard k Finset.univ,
    dist S * ((l i : ℝ) + if i ∈ S then 1 else 0) = h * p i)
