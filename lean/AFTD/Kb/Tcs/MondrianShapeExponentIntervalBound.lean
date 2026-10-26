import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianSortedPairsEqOfShared

/-!
# mondrian_shape_exponent_interval_bound

Topic: combinatorics   Node: 25b1e526419c

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

A family of distinct sorted factor pairs that can be encoded by a chosen side C times p to an exponent in [lo,hi] has at most hi plus one minus lo members.
-/

theorem mondrian_shape_exponent_interval_bound (p n A C lo hi : ℕ) (S : Finset (ℕ × ℕ))
    (hA : 0 < A) (hS : S ⊆ mondrian_factor_shapes n A)
    (g : (ℕ × ℕ) → ℕ) (f : (ℕ × ℕ) → ℕ)
    (hg : ∀ d ∈ S, (g d = d.1 ∨ g d = d.2) ∧ g d = C * p ^ f d)
    (hf : ∀ d ∈ S, lo ≤ f d ∧ f d ≤ hi) : S.card ≤ hi + 1 - lo := by
  have hmap : Set.MapsTo f ↑S ↑(Finset.Icc lo hi) := by
    intro d hd
    exact Finset.mem_Icc.mpr (hf d hd)
  have hinj : Set.InjOn f ↑S := by
    intro x hx y hy he
    obtain ⟨hxp, _, hxo, _⟩ := (mondrian_mem_factor_shapes n A x).mp (hS hx)
    obtain ⟨hyp, _, hyo, _⟩ := (mondrian_mem_factor_shapes n A y).mp (hS hy)
    have hh : g x = g y := by rw [(hg x hx).2, (hg y hy).2, he]
    apply mondrian_sorted_pairs_eq_of_shared x y A hA hxp hyp hxo hyo
    rcases (hg x hx).1 with hhx | hhx <;>
      rcases (hg y hy).1 with hhy | hhy <;> rw [hhx, hhy] at hh <;> tauto
  simpa using Finset.card_le_card_of_injOn f hmap hinj
