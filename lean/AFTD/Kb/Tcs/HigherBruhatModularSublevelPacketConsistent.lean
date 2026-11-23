import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatPacketConsistent
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# higher_bruhat_modular_sublevel_packet_consistent

Topic: combinatorics   Node: e88344a1c2d8

Provenance: helper lemma. arXiv:2611.17465, Section 2.1, Proof of Proposition 2

Let n, k, and c be natural numbers such that 2 ≤ k, k + 1 ≤ n, and c < n. Let E be a family of subsets of Fin n such that every element A ∈ E has cardinality k + 1 and satisfies (∑ a ∈ A, a.val) % n = c. Define X to be the family of subsets A of Fin n of cardinality k + 1 such that, with diff = (∑ a ∈ A, (a.val : ℤ)) - (c : ℤ), diff % (n : ℤ) ≠ 0 and the integer quotient diff / (n : ℤ) is odd. Then the union X ∪ E is packet-consistent.
-/

lemma higher_bruhat_modular_sublevel_packet_consistent_sub_mod_eq_zero (n c s : ℕ) (hs : s % n = c) :
    ((s : ℤ) - (c : ℤ)) % (n : ℤ) = 0 := by
  have h_mod : (s : ℤ) % (n : ℤ) = (c : ℤ) := by
    rw [← hs]
    exact Int.ofNat_mod_ofNat s n
  have h_div : (s : ℤ) = (n : ℤ) * ((s : ℤ) / (n : ℤ)) + (s : ℤ) % (n : ℤ) :=
    (Int.mul_ediv_add_emod (s : ℤ) (n : ℤ)).symm
  rw [h_mod] at h_div
  have h_sub : (s : ℤ) - (c : ℤ) = (n : ℤ) * ((s : ℤ) / (n : ℤ)) := by
    omega
  rw [h_sub]
  exact Int.mul_emod_right (n : ℤ) ((s : ℤ) / (n : ℤ))

lemma higher_bruhat_modular_sublevel_packet_consistent_div_mod_gt (n : ℕ) (hn : 0 < n) (T x_val : ℤ) (hx : 0 ≤ x_val) (_hxn : x_val < (n : ℤ)) :
    let d := T - x_val
    let m := T / (n : ℤ)
    d > m * (n : ℤ) → d / (n : ℤ) = m ∧ d % (n : ℤ) ≠ 0 := by
  intro d m hd
  have hn_pos : 0 < (n : ℤ) := by omega
  have h_div : T = (n : ℤ) * m + T % (n : ℤ) := by
    dsimp [m]
    exact (Int.mul_ediv_add_emod T (n : ℤ)).symm
  have hd' : m * (n : ℤ) < d := hd
  rw [mul_comm] at hd'
  have h_rem1 : 0 ≤ T % (n : ℤ) - x_val := by
    dsimp [d] at hd'
    omega
  have h_rem2 : T % (n : ℤ) - x_val < (n : ℤ) := by
    have := Int.emod_lt_of_pos T hn_pos
    omega
  have h_eq : (T % (n : ℤ) - x_val) + (n : ℤ) * m = d := by
    dsimp [d]
    linarith
  have h_uniq := (Int.ediv_emod_unique hn_pos).mpr ⟨h_eq, h_rem1, h_rem2⟩
  refine ⟨h_uniq.1, ?_⟩
  rw [h_uniq.2]
  dsimp [d] at hd'
  omega

lemma higher_bruhat_modular_sublevel_packet_consistent_div_mod_lt (n : ℕ) (hn : 0 < n) (T x_val : ℤ) (_hx : 0 ≤ x_val) (hxn : x_val < (n : ℤ)) :
    let d := T - x_val
    let m := T / (n : ℤ)
    d < m * (n : ℤ) → d / (n : ℤ) = m - 1 ∧ d % (n : ℤ) ≠ 0 := by
  intro d m hd
  have hn_pos : 0 < (n : ℤ) := by omega
  have h_div : T = (n : ℤ) * m + T % (n : ℤ) := by
    dsimp [m]
    exact (Int.mul_ediv_add_emod T (n : ℤ)).symm
  have hd' : d < m * (n : ℤ) := hd
  rw [mul_comm] at hd'
  have h_rem1 : 0 ≤ T % (n : ℤ) - x_val + (n : ℤ) := by
    have := Int.emod_nonneg T (by omega : (n : ℤ) ≠ 0)
    omega
  have h_rem2 : T % (n : ℤ) - x_val + (n : ℤ) < (n : ℤ) := by
    dsimp [d] at hd'
    omega
  have h_eq : (T % (n : ℤ) - x_val + (n : ℤ)) + (n : ℤ) * (m - 1) = d := by
    dsimp [d]
    linarith
  have h_uniq := (Int.ediv_emod_unique hn_pos).mpr ⟨h_eq, h_rem1, h_rem2⟩
  refine ⟨h_uniq.1, ?_⟩
  rw [h_uniq.2]
  have := Int.emod_nonneg T (by omega : (n : ℤ) ≠ 0)
  omega

/-- Consistency of the union of the alternating sublevel family with any subcollection of the modular level set. -/
lemma higher_bruhat_modular_sublevel_packet_consistent
    (n k c : ℕ) (hk : 2 ≤ k) (hn : k + 1 ≤ n) (hc : c < n)
    (E : Finset (Finset (Fin n)))
    (hE : E ⊆ (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k + 1)).filter
      (fun A => (∑ a ∈ A, a.val) % n = c)) :
    let X : Finset (Finset (Fin n)) :=
      (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k + 1)).filter
        (fun A =>
          let diff : ℤ := (∑ a ∈ A, (a.val : ℤ)) - (c : ℤ)
          diff % (n : ℤ) ≠ 0 ∧ Odd (diff / (n : ℤ)))
    higher_bruhat_packet_consistent n k (X ∪ E) := by
  intro X M hM
  have hn_pos : 0 < n := by omega
  set T : ℤ := (∑ a ∈ M, (a.val : ℤ)) - (c : ℤ)
  set m : ℤ := T / (n : ℤ)
  have hE_diff (A : Finset (Fin n)) (hA : A ∈ E) :
      ((∑ a ∈ A, (a.val : ℤ)) - (c : ℤ)) % (n : ℤ) = 0 := by
    have hA' := hE hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA'
    have hcast : (∑ a ∈ A, (a.val : ℤ)) = ((∑ a ∈ A, a.val : ℕ) : ℤ) := by
      push_cast; rfl
    rw [hcast]
    exact higher_bruhat_modular_sublevel_packet_consistent_sub_mod_eq_zero n c (∑ a ∈ A, a.val) hA'.2
  have h_card (x : Fin n) (hx : x ∈ M) : (M.erase x).card = k + 1 := by
    rw [Finset.card_erase_of_mem hx, hM]
    rfl
  have h_diff_eq (x : Fin n) (hx : x ∈ M) :
      (∑ a ∈ M.erase x, (a.val : ℤ)) - (c : ℤ) = T - (x.val : ℤ) := by
    dsimp [T]
    have h := Finset.sum_erase_add M (fun a : Fin n => (a.val : ℤ)) hx
    linarith
  have h_mem_X (x : Fin n) (hx : x ∈ M) :
      M.erase x ∈ X ↔
        (T - (x.val : ℤ)) % (n : ℤ) ≠ 0 ∧ Odd ((T - (x.val : ℤ)) / (n : ℤ)) := by
    dsimp [X]
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, h_card x hx]
    rw [h_diff_eq x hx]
  by_cases hm : Odd m
  · right
    intro a ha b hb hab hb_union
    rw [Finset.mem_union] at hb_union
    have hb_not_lt : ¬ (T - (b.val : ℤ) < m * (n : ℤ)) := by
      intro h_lt
      have h_div_mod := higher_bruhat_modular_sublevel_packet_consistent_div_mod_lt
        n hn_pos T (b.val : ℤ) (by positivity) (by omega) h_lt
      have h_not_odd : ¬ Odd ((T - (b.val : ℤ)) / (n : ℤ)) := by
        rw [h_div_mod.1, odd_sub_one]
        intro he
        exact (Int.not_even_iff_odd.mpr hm) he
      cases hb_union with
      | inl hX =>
        have := (h_mem_X b hb).mp hX
        exact h_not_odd this.2
      | inr hE_mem =>
        have h_zero := hE_diff (M.erase b) hE_mem
        rw [h_diff_eq b hb] at h_zero
        exact h_div_mod.2 h_zero
    have hb_ge : m * (n : ℤ) ≤ T - (b.val : ℤ) := by omega
    have hab_val : (a.val : ℤ) < (b.val : ℤ) := by omega
    have ha_gt : T - (a.val : ℤ) > m * (n : ℤ) := by omega
    have h_div_mod_a := higher_bruhat_modular_sublevel_packet_consistent_div_mod_gt
      n hn_pos T (a.val : ℤ) (by positivity) (by omega) ha_gt
    have ha_X : M.erase a ∈ X := by
      rw [h_mem_X a ha]
      refine ⟨h_div_mod_a.2, ?_⟩
      rw [h_div_mod_a.1]
      exact hm
    exact Finset.mem_union_left E ha_X
  · left
    intro a ha b hb hab ha_union
    rw [Finset.mem_union] at ha_union
    have ha_not_gt : ¬ (T - (a.val : ℤ) > m * (n : ℤ)) := by
      intro h_gt
      have h_div_mod := higher_bruhat_modular_sublevel_packet_consistent_div_mod_gt
        n hn_pos T (a.val : ℤ) (by positivity) (by omega) h_gt
      have h_not_odd : ¬ Odd ((T - (a.val : ℤ)) / (n : ℤ)) := by
        rw [h_div_mod.1]
        exact hm
      cases ha_union with
      | inl hX =>
        have := (h_mem_X a ha).mp hX
        exact h_not_odd this.2
      | inr hE_mem =>
        have h_zero := hE_diff (M.erase a) hE_mem
        rw [h_diff_eq a ha] at h_zero
        exact h_div_mod.2 h_zero
    have ha_le : T - (a.val : ℤ) ≤ m * (n : ℤ) := by omega
    have hab_val : (a.val : ℤ) < (b.val : ℤ) := by omega
    have hb_lt : T - (b.val : ℤ) < m * (n : ℤ) := by omega
    have h_div_mod_b := higher_bruhat_modular_sublevel_packet_consistent_div_mod_lt
      n hn_pos T (b.val : ℤ) (by positivity) (by omega) hb_lt
    have hb_X : M.erase b ∈ X := by
      rw [h_mem_X b hb]
      refine ⟨h_div_mod_b.2, ?_⟩
      rw [h_div_mod_b.1, odd_sub_one]
      exact Int.not_odd_iff_even.mp hm
    exact Finset.mem_union_left E hb_X
