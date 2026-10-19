import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1OfCardLeTwoMul

/-!
# round_robin_sequence_count_le_two_of_ne_zero

Topic: fair_division   Node: f4a11511b209

Provenance: helper lemma. Step for round_robin_pne_ef1_of_card_le_two_mul_add_one (thread RT-3).

In the Round-Robin sequence of n agents and 2n + 1 goods, every agent other than agent 0 picks at most twice.
-/

theorem round_robin_sequence_count_le_two_of_ne_zero (n : ℕ) [NeZero n] (j : Fin n) (hj : j ≠ 0) :
    (round_robin_sequence n (2 * n + 1)).count j ≤ 2 := by
  set seq := round_robin_sequence n (2 * n + 1) with hseq
  have hlen : seq.length = 2 * n + 1 := rr_l1_seq_length n _
  have ex : ∀ (t : ℕ) (ht : t < seq.length), (seq[t]).val = t % n :=
    fun t ht => rr_l1_seq_getElem n _ t ht
  rw [← List.take_append_drop n seq, List.count_append, ← List.take_append_drop n (seq.drop n),
    List.count_append, List.drop_drop]
  have h1 := rr_l1_count_take_le_one n (2 * n + 1) n le_rfl j
  rw [← hseq] at h1
  have h2 : ((seq.drop n).take n).count j ≤ 1 := by
    apply List.nodup_iff_count_le_one.mp
    rw [List.nodup_iff_injective_getElem]
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [List.length_take, List.length_drop, hlen] at hx hy
    have h1 := congrArg Fin.val hxy
    simp only [List.getElem_take, List.getElem_drop, ex] at h1
    have e1 : (n + x) % n = x := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (n + y) % n = y := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2] at h1
    exact Fin.ext h1
  have h3 : (seq.drop (n + n)).count j = 0 := by
    apply List.count_eq_zero.mpr
    intro hmem
    obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.mp hmem
    simp only [List.length_drop, hlen] at ht
    have h1 := congrArg Fin.val hte
    simp only [List.getElem_drop, ex] at h1
    have : (n + n + t) % n = 0 := by
      have ht0 : t = 0 := by omega
      subst ht0; simp
    rw [this] at h1
    exact hj (Fin.ext h1.symm)
  omega
