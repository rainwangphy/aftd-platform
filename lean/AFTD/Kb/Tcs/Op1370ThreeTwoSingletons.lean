import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370IncomparableTwoSetsCardBound

/-!
# op_1370_three_two_singletons

Topic: combinatorics   Node: 12e88e79307e

Provenance: original. Related work: arXiv:2611.12199, Conjecture 4.3, restricted to three families with two singleton families.

For n at least three, if three mutually strongly incomparable families of subsets of an n-element set have their first two families singleton and the third uncomplemented, then their total size is at most 2^(n-1) - 1.
-/

theorem op_1370_three_two_singletons (n : ℕ) (hn : 3 ≤ n)
    (𝒜 : Fin 3 → Finset (Finset (Fin n)))
    (A B : Finset (Fin n)) (h0 : 𝒜 0 = {A}) (h1 : 𝒜 1 = {B})
    (hunc : is_uncomplemented (𝒜 2)) (hinc : strongly_incomparable 𝒜) :
    ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) - 1 := by
  classical
  have ha : A ∈ 𝒜 0 := by rw [h0]; simp
  have hb : B ∈ 𝒜 1 := by rw [h1]; simp
  have hab := hinc 0 1 (by decide) A ha B hb
  have hba := hinc 1 0 (by decide) B hb A ha
  have hbound := op_1370_incomparable_two_sets_card_bound n hn A B hab hba (𝒜 2) hunc
    (fun S hS => hinc 2 0 (by decide) S hS A ha)
    (fun S hS => hinc 0 2 (by decide) A ha S hS)
    (fun S hS => hinc 2 1 (by decide) S hS B hb)
    (fun S hS => hinc 1 2 (by decide) B hb S hS)
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ]
    omega
  rw [hp] at hbound
  simp only [Fin.sum_univ_three, h0, h1, Finset.card_singleton]
  omega
