import AFTD.Prelude

/-!
# set_system_aura

Topic: combinatorics   Node: 697be9441ceb

Provenance: formalization of a published result. Source: arXiv:2611.13495 Def. 3

Given a natural number r and a finite set of finite subsets S of a type α with decidable equality, the aura of S relative to parameter r is the natural number |⋃ S| + (r - 1) * |S|, where (r - 1) uses natural number subtraction.
-/

/-- The aura of a set system S relative to natural parameter r: |⋃ S| + (r - 1) * |S|. -/
def set_system_aura (r : ℕ) {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : ℕ := (S.biUnion id).card + (r - 1) * S.card
