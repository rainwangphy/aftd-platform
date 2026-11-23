import AFTD.Prelude
import AFTD.Kb.Tcs.CodeMinDist
import AFTD.Kb.Tcs.IsJointPerfectCode
import AFTD.Kb.Tcs.JointCodeDistGe
import AFTD.Kb.Tcs.JointPerfectCodePartition
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting
import AFTD.Kb.Tcs.HammingRing

/-!
# joint_perfect_code_min_dist

Topic: information   Node: 8deddd0e17e8

Provenance: formalization of a published result. Source: arXiv:2611.18156, Proposition IV.2

Given implicit parameters n, q, c, and c', if C : Finset (Fin n → Fin q) is a (c, c') joint perfect code with 2 ≤ C.card, then code_min_dist C (2 * c + c' + 1), and if c' = 0 then 2 * c + c' + 1 is odd.
-/

/-- A non-trivial (c, c') joint perfect code has minimum distance 2c + c' + 1; when c' = 0, this distance is odd. -/
theorem joint_perfect_code_min_dist {n q c c' : ℕ}
    (C : Finset (Fin n → Fin q)) (hC : is_joint_perfect_code c c' C) (hcard : 2 ≤ C.card) :
    code_min_dist C (2 * c + c' + 1) ∧ (c' = 0 → Odd (2 * c + c' + 1)) := by
  have hed : is_joint_error_correcting_detecting c c' C := hC.1
  obtain ⟨x₀, hx₀, x₁, hx₁, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
  have hTne : (C.erase x₀).Nonempty := ⟨x₁, Finset.mem_erase.mpr ⟨hne.symm, hx₁⟩⟩
  obtain ⟨x', hx'T, hmin⟩ := Finset.exists_min_image (C.erase x₀) (fun z => hammingDist x₀ z) hTne
  have hx'C : x' ∈ C := Finset.mem_of_mem_erase hx'T
  have hx'ne : x' ≠ x₀ := (Finset.mem_erase.mp hx'T).1
  have hDge : 2 * c + c' + 1 ≤ hammingDist x₀ x' := joint_code_dist_ge C hed hx₀ hx'C hx'ne.symm
  have hDle : hammingDist x₀ x' ≤ 2 * c + c' + 1 := by
    by_contra hcon
    have hcon' : 2 * c + c' + 1 < hammingDist x₀ x' := by omega
    set Dset := Finset.univ.filter (fun i => x₀ i ≠ x' i) with hDsetdef
    have hDsetcard : Dset.card = hammingDist x₀ x' := rfl
    have hle : c + c' + 1 ≤ Dset.card := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := Dset) (n := c + c' + 1) hle
    set y : Fin n → Fin q := fun i => if i ∈ S then x' i else x₀ i with hydef
    have hdy : hammingDist x₀ y = c + c' + 1 := by
      have hfilter : Finset.univ.filter (fun i => x₀ i ≠ y i) = S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          by_contra hni
          exact hi (by simp [hydef, hni])
        · intro hi
          have hxi : x₀ i ≠ x' i := (Finset.mem_filter.mp (hSsub hi)).2
          simpa [hydef, hi] using hxi
      show (Finset.univ.filter (fun i => x₀ i ≠ y i)).card = c + c' + 1
      rw [hfilter, hScard]
    have hfar : ∀ x ∈ C, c + 1 ≤ hammingDist x y := by
      intro x hxC
      by_cases hxx : x = x₀
      · subst hxx
        rw [hdy]; omega
      · have hxT : x ∈ C.erase x₀ := Finset.mem_erase.mpr ⟨hxx, hxC⟩
        have hDmin : hammingDist x₀ x' ≤ hammingDist x₀ x := hmin x hxT
        have htri : hammingDist x₀ x ≤ hammingDist x₀ y + hammingDist y x :=
          hammingDist_triangle x₀ y x
        rw [hdy, hammingDist_comm y x] at htri
        omega
    have hpart := joint_perfect_code_partition C hC hx₀ y
    rcases hpart with ⟨x, hxC, hball⟩ | hring
    · have hd : hammingDist x y ≤ c := by simpa [hamming_ball] using hball
      have := hfar x hxC
      omega
    · have hd2 : hammingDist x₀ y ≤ c + c' := by
        have h := hring
        simp only [hamming_ring, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h.2
      omega
  refine ⟨?_, ?_⟩
  · refine ⟨⟨x₀, hx₀, x', hx'C, hx'ne.symm, ?_⟩, ?_⟩
    · omega
    · intro x hx y hy hxy
      exact joint_code_dist_ge C hed hx hy hxy
  · intro hc'
    subst hc'
    exact ⟨c, by omega⟩
