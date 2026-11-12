import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_three_two_singletons_sharp

Topic: combinatorics   Node: 5d897126070f

Provenance: original. Related work: arXiv:2611.12199, Proposition 4.2 and Conjecture 4.3; a sharp construction with two singleton families.

For every n at least three there are three nonempty uncomplemented mutually strongly incomparable families of subsets of an n-element set, the first two of which are singleton families, whose total size is exactly 2^(n-1)-1.
-/

theorem op_1370_three_two_singletons_sharp (n : ℕ) (hn : 3 ≤ n) : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin n)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ (𝒜 0).card = 1 ∧ (𝒜 1).card = 1 ∧ (∑ i, (𝒜 i).card) = 2 ^ (n - 1) - 1 := by
  let x : Fin n := ⟨0, by omega⟩
  let y : Fin n := ⟨1, by omega⟩
  let z : Fin n := ⟨2, by omega⟩
  let s : Finset (Fin n) := Finset.univ.erase x
  let T : Finset (Finset (Fin n)) := {∅, {y}, {z}}
  let 𝒜 : Fin 3 → Finset (Finset (Fin n)) := ![ { {x, y} }, { {x, z} }, s.powerset \ T ]
  use 𝒜
  have hx_ne_y : x ≠ y := by dsimp [x, y]; intro h; cases h
  have hx_ne_z : x ≠ z := by dsimp [x, z]; intro h; cases h
  have hy_ne_z : y ≠ z := by dsimp [y, z]; intro h; cases h
  have hT_sub : T ⊆ s.powerset := by
    intro A hA
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · simp [s]
    · simp [s, Finset.mem_powerset, Finset.subset_iff, hx_ne_y.symm]
    · simp [s, Finset.mem_powerset, Finset.subset_iff, hx_ne_z.symm]
  have hT_card : T.card = 3 := by
    dsimp [T]
    have h1 : (∅ : Finset (Fin n)) ∉ ({ {y}, {z} } : Finset (Finset (Fin n))) := by simp
    have h2 : ({y} : Finset (Fin n)) ∉ ({ {z} } : Finset (Finset (Fin n))) := by simp [hy_ne_z]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hA2_card : (s.powerset \ T).card = 2 ^ (n - 1) - 3 := by
    rw [Finset.card_sdiff_of_subset hT_sub, Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin, hT_card]
  have hpow : 4 ≤ 2 ^ (n - 1) := by
    have : 2 ≤ n - 1 := by omega
    calc 4 = 2 ^ 2 := by rfl
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · dsimp [𝒜]; exact Finset.singleton_nonempty _
    · dsimp [𝒜]; exact Finset.singleton_nonempty _
    · dsimp [𝒜]; apply Finset.card_pos.mp; rw [hA2_card]; omega
  · intro i
    fin_cases i
    · intro A hA
      dsimp [𝒜] at hA
      simp only [Finset.mem_singleton] at hA
      subst hA
      intro hAc
      dsimp [𝒜] at hAc
      simp only [Finset.mem_singleton] at hAc
      have hx : x ∈ ({x, y} : Finset (Fin n)) := by simp
      have hx' : x ∉ ({x, y} : Finset (Fin n))ᶜ := by simp
      rw [hAc] at hx'
      exact hx' hx
    · intro A hA
      dsimp [𝒜] at hA
      simp only [Finset.mem_singleton] at hA
      subst hA
      intro hAc
      dsimp [𝒜] at hAc
      simp only [Finset.mem_singleton] at hAc
      have hx : x ∈ ({x, z} : Finset (Fin n)) := by simp
      have hx' : x ∉ ({x, z} : Finset (Fin n))ᶜ := by simp
      rw [hAc] at hx'
      exact hx' hx
    · intro A hA
      dsimp [𝒜] at hA
      simp only [Finset.mem_sdiff, Finset.mem_powerset] at hA
      intro hAc
      dsimp [𝒜] at hAc
      simp only [Finset.mem_sdiff, Finset.mem_powerset] at hAc
      have hxA : x ∉ A := by
        intro h
        have := hA.1 h
        simp [s] at this
      have hxAc : x ∈ Aᶜ := by simp [hxA]
      have hx_not : x ∉ Aᶜ := by
        intro h
        have := hAc.1 h
        simp [s] at this
      exact hx_not hxAc
  · intro i j hij
    fin_cases i <;> fin_cases j
    · intro A hA B hB hsub; exact (hij rfl).elim
    · intro A hA B hB hsub
      dsimp [𝒜] at hA hB
      simp only [Finset.mem_singleton] at hA hB
      subst hA hB
      have : y ∈ ({x, z} : Finset (Fin n)) := hsub (by simp)
      simp [hx_ne_y.symm, hy_ne_z] at this
    · intro A hA B hB hsub
      dsimp [𝒜] at hA hB
      simp only [Finset.mem_singleton] at hA
      simp only [Finset.mem_sdiff, Finset.mem_powerset] at hB
      subst hA
      have hx_in_A : x ∈ ({x, y} : Finset (Fin n)) := by simp
      have hx_in_B : x ∈ B := hsub hx_in_A
      have hx_in_s : x ∈ s := hB.1 hx_in_B
      simp [s] at hx_in_s
    · intro A hA B hB hsub
      dsimp [𝒜] at hA hB
      simp only [Finset.mem_singleton] at hA hB
      subst hA hB
      have hz : z ∈ ({x, y} : Finset (Fin n)) := hsub (by simp)
      simp [hx_ne_z.symm, hy_ne_z.symm] at hz
    · intro A hA B hB hsub; exact (hij rfl).elim
    · intro A hA B hB hsub
      dsimp [𝒜] at hA hB
      simp only [Finset.mem_singleton] at hA
      simp only [Finset.mem_sdiff, Finset.mem_powerset] at hB
      subst hA
      have hx_in_A : x ∈ ({x, z} : Finset (Fin n)) := by simp
      have hx_in_B : x ∈ B := hsub hx_in_A
      have hx_in_s : x ∈ s := hB.1 hx_in_B
      simp [s] at hx_in_s
    · intro A hA B hB hsub
      dsimp [𝒜] at hA hB
      simp only [Finset.mem_sdiff, Finset.mem_powerset] at hA
      simp only [Finset.mem_singleton] at hB
      subst hB
      have hA_sub_y : A ⊆ {y} := by
        intro u hu
        have hu_xy := hsub hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu_xy
        rcases hu_xy with rfl | rfl
        · have : x ∈ s := hA.1 hu
          simp [s] at this
        · simp
      rcases Finset.subset_singleton_iff.mp hA_sub_y with rfl | rfl
      · exact hA.2 (by simp [T])
      · exact hA.2 (by simp [T])
    · intro A hA B hB hsub
      dsimp [𝒜] at hA hB
      simp only [Finset.mem_sdiff, Finset.mem_powerset] at hA
      simp only [Finset.mem_singleton] at hB
      subst hB
      have hA_sub_z : A ⊆ {z} := by
        intro u hu
        have hu_xz := hsub hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu_xz
        rcases hu_xz with rfl | rfl
        · have : x ∈ s := hA.1 hu
          simp [s] at this
        · simp
      rcases Finset.subset_singleton_iff.mp hA_sub_z with rfl | rfl
      · exact hA.2 (by simp [T])
      · exact hA.2 (by simp [T])
    · intro A hA B hB hsub; exact (hij rfl).elim
  · dsimp [𝒜]; exact Finset.card_singleton _
  · dsimp [𝒜]; exact Finset.card_singleton _
  · rw [Fin.sum_univ_three]
    have h0 : (𝒜 0).card = 1 := by dsimp [𝒜]; exact Finset.card_singleton _
    have h1 : (𝒜 1).card = 1 := by dsimp [𝒜]; exact Finset.card_singleton _
    have h2 : (𝒜 2).card = 2 ^ (n - 1) - 3 := by dsimp [𝒜]; exact hA2_card
    rw [h0, h1, h2]
    omega
