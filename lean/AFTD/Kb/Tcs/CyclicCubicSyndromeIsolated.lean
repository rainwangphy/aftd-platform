import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicSyndrome

/-!
# cyclic_cubic_syndrome_isolated

Topic: quantum   Node: 76321750d190

Provenance: helper lemma. step towards cyclic_cubic_parity_repr_eval_zero

For n ≥ 6 and any x : Fin n, the cyclic cubic syndrome of {j, (x-1)%n, (x+1)%n} is 0 for all j ≠ x.
-/

private lemma cyclic_cubic_syndrome_isolated_aux_pred_succ (n : ℕ) (a : Fin n) :
    ((a.val + n - 1) % n + 1) % n = a.val := by
  rw [Nat.mod_add_mod]
  have h : a.val + n - 1 + 1 = a.val + n := by omega
  rw [h, show (a.val + n) % n = a.val % n from by
    simpa using Nat.add_mul_mod_self_left a.val 1 n]
  exact Nat.mod_eq_of_lt a.isLt

private lemma cyclic_cubic_syndrome_isolated_aux_gap (n : ℕ) (hn : 6 ≤ n)
    (kv pv qv i i' : ℕ) (hi : i ≤ 2) (hi' : i' ≤ 2)
    (hp : pv ≡ kv + i [MOD n]) (hq : qv ≡ kv + i' [MOD n])
    (hpq : qv ≡ pv + 2 [MOD n]) : i = 0 ∧ i' = 2 := by
  have hstep : pv + 2 ≡ kv + (i + 2) [MOD n] := by
    simpa [Nat.add_assoc] using hp.add_right 2
  have key : qv ≡ kv + (i + 2) [MOD n] := hpq.trans hstep
  have key0 : kv + i' ≡ kv + (i + 2) [MOD n] := hq.symm.trans key
  have key2 : i' ≡ i + 2 [MOD n] := Nat.ModEq.add_left_cancel' kv key0
  have heq : i' = i + 2 := Nat.ModEq.eq_of_lt_of_lt key2 (by omega) (by omega)
  omega

private lemma cyclic_cubic_syndrome_isolated_aux_mem_gap (n : ℕ) (k a k1 k2 : Fin n)
    (h1 : k1.val = (k.val + 1) % n) (h2 : k2.val = (k.val + 2) % n)
    (ha : a ∈ ({k, k1, k2} : Finset (Fin n))) :
    ∃ i : ℕ, i ≤ 2 ∧ a.val ≡ k.val + i [MOD n] := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with h | h | h
  · refine ⟨0, by norm_num, ?_⟩
    rw [h]
    show k.val % n = (k.val + 0) % n
    rw [Nat.add_zero]
  · refine ⟨1, by norm_num, ?_⟩
    rw [h, h1]
    exact Nat.mod_modEq _ _
  · refine ⟨2, by norm_num, ?_⟩
    rw [h, h2]
    exact Nat.mod_modEq _ _

private lemma cyclic_cubic_syndrome_isolated_aux_small_congr (n : ℕ) (hn : 6 ≤ n)
    (a b : ℕ) (hlt : a < b) (hle : b ≤ a + 5) (h : a ≡ b [MOD n]) : False := by
  have hd : n ∣ b - a := h.dvd'
  have hpos : 0 < b - a := by omega
  have h5 : b - a ≤ 5 := by omega
  have := Nat.le_of_dvd hpos hd
  omega

/-- For n ≥ 6, any cyclic consecutive triple containing both (x-1)%n and (x+1)%n must have third element x, so the syndrome is 0 for j ≠ x. -/
theorem cyclic_cubic_syndrome_isolated (n : ℕ) (hn : 6 ≤ n) (x j : Fin n) (hjx : j ≠ x) : cyclic_cubic_syndrome n {j, ⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩, ⟨(x.val + 1) % n, Nat.mod_lt _ (by omega)⟩} = 0 := by
  unfold cyclic_cubic_syndrome
  split
  · rename_i h
    rcases h with ⟨k, hk⟩
    let p : Fin n := ⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩
    let q : Fin n := ⟨(x.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    let k1 : Fin n := ⟨(k.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    let k2 : Fin n := ⟨(k.val + 2) % n, Nat.mod_lt _ (by omega)⟩
    have hk' : ({j, p, q} : Finset (Fin n)) = {k, k1, k2} := hk
    have hp_mem : p ∈ ({k, k1, k2} : Finset (Fin n)) := by rw [← hk']; simp
    have hq_mem : q ∈ ({k, k1, k2} : Finset (Fin n)) := by rw [← hk']; simp
    obtain ⟨i, hi, hpi⟩ := cyclic_cubic_syndrome_isolated_aux_mem_gap n k p k1 k2 rfl rfl hp_mem
    obtain ⟨i', hi', hqi⟩ := cyclic_cubic_syndrome_isolated_aux_mem_gap n k q k1 k2 rfl rfl hq_mem
    have hpv : p.val = (x.val + n - 1) % n := rfl
    have hqv : q.val = (x.val + 1) % n := rfl
    have hpq : q.val ≡ p.val + 2 [MOD n] := by
      have h1 : p.val ≡ x.val + n - 1 [MOD n] := by rw [hpv]; exact Nat.mod_modEq _ _
      have h2 : q.val ≡ x.val + 1 [MOD n] := by rw [hqv]; exact Nat.mod_modEq _ _
      have h3 : p.val + 2 ≡ x.val + n - 1 + 2 [MOD n] := h1.add_right 2
      have he : x.val + n - 1 + 2 = (x.val + 1) + n := by omega
      rw [he] at h3
      have h4 : (x.val + 1) + n ≡ x.val + 1 [MOD n] := by
        simpa using Nat.add_mul_mod_self_left (x.val + 1) 1 n
      exact h2.trans (h3.trans h4).symm
    obtain ⟨hi0, hi'2⟩ := cyclic_cubic_syndrome_isolated_aux_gap n hn k.val p.val q.val i i' hi hi' hpi hqi hpq
    have hp0 : p.val ≡ k.val [MOD n] := by simpa [hi0] using hpi
    have hq2 : q.val ≡ k.val + 2 [MOD n] := by simpa [hi'2] using hqi
    have hk1mem : k1 ∈ ({j, p, q} : Finset (Fin n)) := by rw [hk']; simp
    have hk1k : k1.val ≡ k.val + 1 [MOD n] := by
      show k1.val % n = (k.val + 1) % n
      rw [show k1.val = (k.val + 1) % n from rfl]
      exact Nat.mod_modEq _ _
    have hjp : j = k1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk1mem
      rcases hk1mem with hh | hh | hh
      · exact hh.symm
      · exfalso
        have hv : k1.val = p.val := congrArg Fin.val hh
        rw [hv] at hk1k
        exact cyclic_cubic_syndrome_isolated_aux_small_congr n hn k.val (k.val + 1) (by omega) (by omega)
          (hp0.symm.trans hk1k)
      · exfalso
        have hv : k1.val = q.val := congrArg Fin.val hh
        rw [hv] at hk1k
        exact cyclic_cubic_syndrome_isolated_aux_small_congr n hn (k.val + 1) (k.val + 2) (by omega) (by omega)
          (hk1k.symm.trans hq2)
    have hxmod : x.val ≡ k.val + 1 [MOD n] := by
      have h := cyclic_cubic_syndrome_isolated_aux_pred_succ n x
      have hxp : x.val ≡ p.val + 1 [MOD n] := by
        show x.val % n = (p.val + 1) % n
        rw [Nat.mod_eq_of_lt x.isLt]
        exact h.symm
      exact hxp.trans (hp0.add_right 1)
    have hjmod : j.val ≡ k.val + 1 [MOD n] := by
      rw [hjp]
      exact hk1k
    have heq : x.val = j.val := Nat.ModEq.eq_of_lt_of_lt (hxmod.trans hjmod.symm) x.isLt j.isLt
    exact absurd (Fin.ext heq.symm) hjx
  · rfl
