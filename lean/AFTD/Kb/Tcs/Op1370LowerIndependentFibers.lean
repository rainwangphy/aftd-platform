import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op1370_lower_independent_fibers

Topic: combinatorics   Node: d90b5692069b

Provenance: helper lemma. A coordinate-slice equality lemma for a balanced-case route to OP-1370, arXiv:2611.12199, Conjecture 4.3.

For two downward-closed families on a finite Boolean cube that attain equality in the uniform correlation inequality, at every coordinate the two slices coincide for at least one family.
-/

open Finset
set_option maxHeartbeats 2000000

theorem op1370_lower_independent_fibers (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset (Fin n))))
    (hℬ : IsLowerSet (ℬ : Set (Finset (Fin n))))
    (hEq : 𝒜.card * ℬ.card = 2 ^ n * (𝒜 ∩ ℬ).card) (x : Fin n) :
    𝒜.memberSubfamily x = 𝒜.nonMemberSubfamily x ∨
      ℬ.memberSubfamily x = ℬ.nonMemberSubfamily x := by
  classical
  let s : Finset (Fin n) := Finset.univ.erase x
  have hs : s.card = n - 1 := by simp [s]
  have h0 (𝒞 : Finset (Finset (Fin n))) : ∀ t ∈ 𝒞.nonMemberSubfamily x, t ⊆ s := by
    intro t ht y hy
    rw [mem_nonMemberSubfamily] at ht
    simp only [s, mem_erase, mem_univ, and_true]
    intro hxy
    exact ht.2 (hxy ▸ hy)
  have h1 (𝒞 : Finset (Finset (Fin n))) : ∀ t ∈ 𝒞.memberSubfamily x, t ⊆ s := by
    intro t ht y hy
    rw [mem_memberSubfamily] at ht
    simp only [s, mem_erase, mem_univ, and_true]
    intro hxy
    exact ht.2 (hxy ▸ hy)
  have hAsub : 𝒜.memberSubfamily x ⊆ 𝒜.nonMemberSubfamily x := h𝒜.memberSubfamily_subset_nonMemberSubfamily
  have hBsub : ℬ.memberSubfamily x ⊆ ℬ.nonMemberSubfamily x := hℬ.memberSubfamily_subset_nonMemberSubfamily
  have hA := card_le_card hAsub
  have hB := card_le_card hBsub
  have h00 := h𝒜.nonMemberSubfamily.le_card_inter_finset' hℬ.nonMemberSubfamily (h0 𝒜) (h0 ℬ)
  have h11 := h𝒜.memberSubfamily.le_card_inter_finset' hℬ.memberSubfamily (h1 𝒜) (h1 ℬ)
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hp : 2 ^ n = 2 * 2 ^ s.card := by
    rw [hs, Nat.mul_comm (2 : ℕ) (2 ^ (n - 1)), ← pow_succ, Nat.sub_add_cancel hn]
  have hEq' := hEq
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily x 𝒜,
      ← card_memberSubfamily_add_card_nonMemberSubfamily x ℬ,
      ← card_memberSubfamily_add_card_nonMemberSubfamily x (𝒜 ∩ ℬ),
      memberSubfamily_inter, nonMemberSubfamily_inter, hp] at hEq'
  by_contra h
  push_neg at h
  have ha : (𝒜.memberSubfamily x).card < (𝒜.nonMemberSubfamily x).card := by
    exact Finset.card_lt_card (lt_of_le_of_ne hAsub h.1)
  have hb : (ℬ.memberSubfamily x).card < (ℬ.nonMemberSubfamily x).card := by
    exact Finset.card_lt_card (lt_of_le_of_ne hBsub h.2)
  nlinarith
