import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370BalancedCrossIncomparableHub

/-!
# op_1370_balanced_three_families_exclusion

Topic: combinatorics   Node: 61b9bb9b8a8e

Provenance: helper lemma. Balanced-case consequence of the inclusion-hub route for OP-1370, arXiv:2611.12199, Conjecture 4.3; compare https://arxiv.org/abs/1104.3988.

There are no three nonempty mutually strongly incomparable families of subsets of an n-element set, for n at least two, such that the first has 2^(n-2) members and the other two together have 2^(n-2) members. No uncomplementedness assumption is required.
-/

theorem op_1370_balanced_three_families_exclusion (n : ℕ) (hn : 2 ≤ n)
    (𝒜 : Fin 3 → Finset (Finset (Fin n)))
    (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜)
    (h0 : (𝒜 0).card = 2 ^ (n - 2))
    (h12 : (𝒜 1).card + (𝒜 2).card = 2 ^ (n - 2)) : False := by
  classical
  set G := 𝒜 1 ∪ 𝒜 2 with hGdef
  have hdisj : Disjoint (𝒜 1) (𝒜 2) := by
    rw [Finset.disjoint_left]
    intro A hA1 hA2
    exact hinc 1 2 (by decide) A hA1 A hA2 (Finset.Subset.refl A)
  have hGcard : G.card = 2 ^ (n - 2) := by
    rw [hGdef, Finset.card_union_of_disjoint hdisj, h12]
  have hcross : ∀ A ∈ 𝒜 0, ∀ B ∈ G, ¬ A ⊆ B ∧ ¬ B ⊆ A := by
    intro A hA B hB
    rw [hGdef, Finset.mem_union] at hB
    rcases hB with hB | hB
    · exact ⟨hinc 0 1 (by decide) A hA B hB, hinc 1 0 (by decide) B hB A hA⟩
    · exact ⟨hinc 0 2 (by decide) A hA B hB, hinc 2 0 (by decide) B hB A hA⟩
  obtain ⟨Z, hZ, hhub⟩ :=
    op1370_balanced_cross_incomparable_hub n hn (𝒜 0) G hcross h0 hGcard
  rw [hGdef, Finset.mem_union] at hZ
  rcases hZ with hZ1 | hZ2
  · obtain ⟨X, hX⟩ := hne 2
    obtain ⟨W, hW, hXW, hZW⟩ := hhub X (by rw [hGdef, Finset.mem_union]; exact Or.inr hX)
    rw [hGdef, Finset.mem_union] at hW
    rcases hW with hW1 | hW2
    · exact hinc 2 1 (by decide) X hX W hW1 hXW
    · exact hinc 1 2 (by decide) Z hZ1 W hW2 hZW
  · obtain ⟨X, hX⟩ := hne 1
    obtain ⟨W, hW, hXW, hZW⟩ := hhub X (by rw [hGdef, Finset.mem_union]; exact Or.inl hX)
    rw [hGdef, Finset.mem_union] at hW
    rcases hW with hW1 | hW2
    · exact hinc 2 1 (by decide) Z hZ2 W hW1 hZW
    · exact hinc 1 2 (by decide) X hX W hW2 hXW
