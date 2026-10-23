import AFTD.Prelude

/-!
# circulant_cycle_not_all_edge_steps

Topic: graphs   Node: 482bfc356b28

Provenance: helper lemma. step towards circulant_mixed_graph_no_cycle_lt_g

An injective sequence on Fin N cannot have every cyclic step equal to m when t ≥ 3 and N = 2m, because two steps of jump m return to the starting vertex.
-/

lemma circulant_cycle_not_all_edge_steps_step {N m : ℕ} (hN : N = 2 * m) (hm : 0 < m)
    {a b : Fin N} (h : (b - a).val = m) :
    (b.val : ℕ) ≡ a.val + m [MOD N] := by
  have hsub : (N - a.val + b.val) % N = m := by
    simpa [Fin.val_sub] using h
  have hmN : m < N := by omega
  have hmod : N - a.val + b.val ≡ m [MOD N] := by
    rw [Nat.ModEq, hsub, Nat.mod_eq_of_lt hmN]
  have h1 : N + b.val ≡ a.val + m [MOD N] := by
    have := Nat.ModEq.add_left a.val hmod
    have hEq : a.val + (N - a.val + b.val) = N + b.val := by omega
    simpa [hEq] using this
  have hN0 : N ≡ 0 [MOD N] := by rw [Nat.ModEq, Nat.mod_self, Nat.zero_mod]
  have hNB : N + b.val ≡ b.val [MOD N] := by
    simpa using Nat.ModEq.add hN0 (Nat.ModEq.refl b.val)
  exact hNB.symm.trans h1

lemma circulant_cycle_not_all_edge_steps_rot_two_ne {t : ℕ} (ht : 3 ≤ t) (i : Fin t) :
    finRotate t (finRotate t i) ≠ i := by
  haveI : NeZero t := ⟨by omega⟩
  intro h
  rw [finRotate_apply, finRotate_apply] at h
  have hv : (↑((i + 1) + 1) : ℕ) = ↑i := by rw [h]
  rw [Fin.val_add, Fin.val_add] at hv
  norm_num at hv
  have hmod : ↑i + 2 ≡ ↑i [MOD t] := by
    rw [Nat.ModEq, hv, Nat.mod_eq_of_lt i.isLt]
  have h2 : 2 ≡ 0 [MOD t] := by
    exact Nat.ModEq.add_left_cancel' (↑i) hmod
  have hdvd : t ∣ 2 := Nat.modEq_zero_iff_dvd.mp h2
  have hle : t ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- An injective sequence on Fin N cannot have every cyclic step equal to m when t ≥ 3 and N = 2m, because two steps of jump m return to the starting vertex. -/
theorem circulant_cycle_not_all_edge_steps {t N m : ℕ} (ht : 3 ≤ t) (hN : N = 2 * m) (hm : 0 < m)
    (x : Fin t → Fin N) (hinj : Function.Injective x) :
    ¬ (∀ i : Fin t, (x (finRotate t i) - x i).val = m) := by
  intro h
  let i : Fin t := ⟨0, by omega⟩
  have h1 : (x (finRotate t i)).val ≡ (x i).val + m [MOD N] :=
    circulant_cycle_not_all_edge_steps_step hN hm (h i)
  have h2 : (x (finRotate t (finRotate t i))).val ≡ (x (finRotate t i)).val + m [MOD N] :=
    circulant_cycle_not_all_edge_steps_step hN hm (h (finRotate t i))
  have hC : (x (finRotate t (finRotate t i))).val ≡ (x i).val [MOD N] := by
    have h1' : (x (finRotate t i)).val + m ≡ (x i).val + m + m [MOD N] := by
      simpa [Nat.add_assoc] using Nat.ModEq.add_right m h1
    have hC' : (x (finRotate t (finRotate t i))).val ≡ (x i).val + m + m [MOD N] := h2.trans h1'
    have hAN : (x i).val + m + m ≡ (x i).val [MOD N] := by
      have hN0 : N ≡ 0 [MOD N] := by rw [Nat.ModEq, Nat.mod_self, Nat.zero_mod]
      have h := Nat.ModEq.add (Nat.ModEq.refl (x i).val) hN0
      have hAN' : (x i).val + N ≡ (x i).val [MOD N] := by simpa using h
      rw [show (x i).val + m + m = (x i).val + N by omega]
      exact hAN'
    exact hC'.trans hAN
  have hx : x (finRotate t (finRotate t i)) = x i := by
    apply Fin.ext
    exact Nat.ModEq.eq_of_lt_of_lt hC (x _).isLt (x i).isLt
  have hperm : finRotate t (finRotate t i) = i := hinj hx
  exact (circulant_cycle_not_all_edge_steps_rot_two_ne ht i) hperm
