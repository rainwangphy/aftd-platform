import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_has_no_unique_sums_exists_rep_ne

Topic: combinatorics   Node: 317dc99927e2

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

If A has no unique sums and a, b ∈ A, then the sum a + b has a second representation c + d with c, d ∈ A all four of c, d distinct from a and b.
-/

/-- In a NUS set every sum of two elements has a repair whose two entries avoid both summands. -/
theorem finset_has_no_unique_sums_exists_rep_ne {G : Type*} [AddCancelCommMonoid G] [DecidableEq G]
    {A : Finset G} (hA : finset_has_no_unique_sums A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    ∃ c ∈ A, ∃ d ∈ A, a + b = c + d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  classical
  have h2 := hA.2 a ha b hb
  unfold finset_unordered_sum_rep_count at h2
  have h1 : 1 < (A.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = a + b)).card := by
    omega
  obtain ⟨z, hz, hz0⟩ := Finset.exists_mem_ne h1 (Sym2.mk a b)
  rw [Finset.mem_filter] at hz
  induction z using Sym2.ind with
  | h u v =>
    simp only [Sym2.lift_mk] at hz
    obtain ⟨hzA, huv⟩ := hz
    rw [Finset.mk_mem_sym2_iff] at hzA
    obtain ⟨hu, hv⟩ := hzA
    refine ⟨u, hu, v, hv, huv.symm, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hz0
      have hv_eq : v = b := by
        rw [h] at huv
        exact add_left_cancel huv
      subst h
      subst hv_eq
      rfl
    · intro h
      apply hz0
      have hv_eq : v = a := by
        rw [h, add_comm a b] at huv
        exact add_left_cancel huv
      subst h
      subst hv_eq
      exact Sym2.eq_swap
    · intro h
      apply hz0
      have hu_eq : u = b := by
        rw [h, add_comm a b] at huv
        exact add_right_cancel huv
      subst h
      subst hu_eq
      exact Sym2.eq_swap
    · intro h
      apply hz0
      have hu_eq : u = a := by
        rw [h] at huv
        exact add_right_cancel huv
      subst h
      subst hu_eq
      rfl
