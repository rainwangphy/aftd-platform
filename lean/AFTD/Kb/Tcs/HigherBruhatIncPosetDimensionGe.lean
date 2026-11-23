import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatIncPosetDimensionGeCardOfBooleanSubposet
import AFTD.Kb.Tcs.HigherBruhatModularSublevelPacketConsistent
import AFTD.Kb.Tcs.HigherBruhatExistsModularLevelSetCardGe
import AFTD.Kb.Tcs.HigherBruhatPacketConsistent
import AFTD.Kb.Tcs.PosetDimension
import AFTD.Kb.Tcs.HigherBruhatIncLe
import AFTD.Kb.Tcs.HigherBruhatInc

/-!
# higher_bruhat_inc_poset_dimension_ge

Topic: combinatorics   Node: e82ec3b0898f

Provenance: formalization of a published result. Source: arXiv:2611.17465, Proposition 2

For integers k ≥ 2 and n ≥ k+1, the Dushnik–Miller dimension of the inclusion higher Bruhat order B_inc(n, k) satisfies dim B_inc(n, k) ≥ ⌈(1/n) * choose(n, k+1)⌉.
-/

/-- Modular level set lower bound on the Dushnik-Miller dimension of the inclusion higher Bruhat order B_inc(n, k). -/
theorem higher_bruhat_inc_poset_dimension_ge (n k : ℕ) (hk : 2 ≤ k) (hn : k + 1 ≤ n) :
    Nat.ceil ((n.choose (k + 1) : ℝ) / (n : ℝ)) ≤ poset_dimension (higher_bruhat_inc_le n k) := by
  have hk0 : 0 < k := by omega
  have hn0 : 0 < n := by omega
  obtain ⟨c, hc, hcard⟩ := higher_bruhat_exists_modular_level_set_card_ge n k hn0 hk0
  set S : Finset (Finset (Fin n)) :=
    (Finset.univ.filter (fun A => A.card = k + 1)).filter (fun A => (∑ a ∈ A, a.val) % n = c)
  set X : Finset (Finset (Fin n)) :=
    (Finset.univ.filter (fun A => A.card = k + 1)).filter (fun A =>
      let diff : ℤ := (∑ a ∈ A, (a.val : ℤ)) - (c : ℤ)
      diff % (n : ℤ) ≠ 0 ∧ Odd (diff / (n : ℤ)))
  have hX : ∀ A ∈ X, A.card = k + 1 := by
    intro A hA
    rw [Finset.mem_filter] at hA
    have hA1 := hA.1
    rw [Finset.mem_filter] at hA1
    exact hA1.2
  have hS : ∀ A ∈ S, A.card = k + 1 := by
    intro A hA
    rw [Finset.mem_filter] at hA
    have hA1 := hA.1
    rw [Finset.mem_filter] at hA1
    exact hA1.2
  have hdisj : Disjoint X S := by
    rw [Finset.disjoint_iff_ne]
    intro A hA B hB hAB
    subst hAB
    rw [Finset.mem_filter] at hA hB
    have hA_cond := hA.2
    have hB_cond := hB.2
    dsimp only at hA_cond hB_cond
    have hmod : (((∑ a ∈ A, a.val : ℕ) : ℤ) - (c : ℤ)) % (n : ℤ) = 0 := by
      have hs' : ((∑ a ∈ A, a.val : ℕ) : ℤ) % (n : ℤ) = (c : ℤ) := by
        rw [← Int.natCast_emod, hB_cond]
      have hc' : (c : ℤ) % (n : ℤ) = (c : ℤ) := by
        rw [← Int.natCast_emod, Nat.mod_eq_of_lt hc]
      rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      rw [hs', hc']
    have hcast : (∑ a ∈ A, (a.val : ℤ)) = ((∑ a ∈ A, a.val : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hcast] at hA_cond
    exact hA_cond.1 hmod
  have hcons : ∀ E ⊆ S, higher_bruhat_packet_consistent n k (X ∪ E) := by
    intro E hE
    exact higher_bruhat_modular_sublevel_packet_consistent n k c hk hn hc E hE
  have hdim := higher_bruhat_inc_poset_dimension_ge_card_of_boolean_subposet n k X S hX hS hdisj hcons
  exact le_trans hcard hdim
