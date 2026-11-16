import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op1370_maximal_free_region_saturation

Topic: combinatorics   Node: 5b5c9787039c

Provenance: helper lemma.

In a system reaching any valid total-size upper bound, a set incomparable to all other colors belongs to its color either directly or through its complement.
-/

open Finset

theorem op1370_maximal_free_region_saturation
    (n t : ℕ) (hn : 0 < n) (𝒜 : Fin t → Finset (Finset (Fin n)))
    (hunc : ∀ i, is_uncomplemented (𝒜 i))
    (hinc : strongly_incomparable 𝒜)
    (K : ℕ)
    (hupper : ∀ B : Fin t → Finset (Finset (Fin n)),
      (∀ i, is_uncomplemented (B i)) → strongly_incomparable B →
      (∑ i, (B i).card) ≤ K)
    (heq : (∑ i, (𝒜 i).card) = K)
    (i : Fin t) (S : Finset (Fin n))
    (hfree : ∀ j, j ≠ i → ∀ T ∈ 𝒜 j, ¬ S ⊆ T ∧ ¬ T ⊆ S) :
    S ∈ 𝒜 i ∨ Sᶜ ∈ 𝒜 i := by
  classical
  by_cases hS : S ∈ 𝒜 i
  · exact Or.inl hS
  by_cases hSc : Sᶜ ∈ 𝒜 i
  · exact Or.inr hSc
  exfalso
  have hnself : S ≠ Sᶜ := by
    intro he
    let x : Fin n := ⟨0, hn⟩
    have hx : x ∈ S ↔ x ∉ S := by
      have hx' := congrArg (fun T : Finset (Fin n) => x ∈ T) he
      simpa using hx'
    by_cases hs : x ∈ S
    · exact (hx.mp hs) hs
    · exact hs (hx.mpr hs)
  let 𝒜' := Function.update 𝒜 i (insert S (𝒜 i))
  have hunc' : ∀ j, is_uncomplemented (𝒜' j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [𝒜', Function.update_self]
      intro T hT hTc
      rcases mem_insert.mp hT with hTS | hT
      · subst T
        rcases mem_insert.mp hTc with hEq | hTc
        · exact hnself hEq.symm
        · exact hSc hTc
      · rcases mem_insert.mp hTc with hEq | hTc
        · have hTSc : T = Sᶜ := by
            have hh := congrArg (fun R : Finset (Fin n) => Rᶜ) hEq
            simpa using hh
          exact hSc (hTSc ▸ hT)
        · exact hunc i T hT hTc
    · simpa [𝒜', Function.update_of_ne hj] using hunc j
  have hinc' : strongly_incomparable 𝒜' := by
    intro j k hjk U hU V hV hUV
    by_cases hj : j = i
    · subst j
      have hk : k ≠ i := Ne.symm hjk
      have hU' : U ∈ insert S (𝒜 i) := by simpa [𝒜'] using hU
      have hV' : V ∈ 𝒜 k := by simpa [𝒜', Function.update_of_ne hk] using hV
      rcases mem_insert.mp hU' with rfl | hU'
      · exact (hfree k hk V hV').1 hUV
      · exact hinc i k hjk U hU' V hV' hUV
    · by_cases hk : k = i
      · subst k
        have hU' : U ∈ 𝒜 j := by simpa [𝒜', Function.update_of_ne hj] using hU
        have hV' : V ∈ insert S (𝒜 i) := by simpa [𝒜'] using hV
        rcases mem_insert.mp hV' with rfl | hV'
        · exact (hfree j hj U hU').2 hUV
        · exact hinc j i hjk U hU' V hV' hUV
      · have hU' : U ∈ 𝒜 j := by simpa [𝒜', Function.update_of_ne hj] using hU
        have hV' : V ∈ 𝒜 k := by simpa [𝒜', Function.update_of_ne hk] using hV
        exact hinc j k hjk U hU' V hV' hUV
  have hcard : ∀ j, (𝒜' j).card = (𝒜 j).card + if j = i then 1 else 0 := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [𝒜', hS]
    · simp [𝒜', Function.update_of_ne hj, hj]
  have hsum : (∑ j, (𝒜' j).card) = (∑ j, (𝒜 j).card) + 1 := by
    simp_rw [hcard]
    simp [Finset.sum_add_distrib]
  have hup := hupper 𝒜' hunc' hinc'
  have hbad : K + 1 ≤ K := by simpa [hsum, heq] using hup
  exact Nat.not_succ_le_self K (by simpa [Nat.add_comm] using hbad)
