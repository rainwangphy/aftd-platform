import AFTD.Prelude

/-!
# has_fractional_matching

Topic: social_choice   Node: b1932158def7

Provenance: formalization of a published result. Source: arXiv:2610.26535 Section 2.2

Given finite types V and C, a profile prof : V → LinearOrder C assigning a linear order to each voter v in V, voter weights p : V → ℝ, candidate weights q : C → ℝ, and a candidate a : C, has_fractional_matching prof p q a asserts the existence of a function w : V → C → ℝ such that for all v and c, 0 ≤ w v c, whenever 0 < w v c candidate c is weakly below a under the linear order prof v (that is, (prof v).le c a), for every voter v the sum of w v c over all c in C equals p v, and for every candidate c the sum of w v c over all v in V equals q c.
-/

/-- Existence of a fractional perfect matching in the domination graph of candidate a. -/
def has_fractional_matching {V C : Type*} [Fintype V] [Fintype C]
    (prof : V → LinearOrder C) (p : V → ℝ) (q : C → ℝ) (a : C) : Prop :=
  ∃ w : V → C → ℝ,
    (∀ v c, 0 ≤ w v c) ∧
    (∀ v c, 0 < w v c → (prof v).le c a) ∧
    (∀ v, ∑ c : C, w v c = p v) ∧
    (∀ c, ∑ v : V, w v c = q c)
