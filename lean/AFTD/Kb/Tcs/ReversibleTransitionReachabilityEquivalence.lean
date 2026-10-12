import AFTD.Prelude

/-!
# reversible_transition_reachability_equivalence

Topic: space_complexity   Node: a3b98e10bc67

Provenance: original. Related work: Lange, McKenzie, Tapp 1997, Reversible Space Equals Deterministic Space; Sipser, Section 8.2

For any finite type V and any injective transition function f : V → V, the reachability relation (fun s t => ∃ m : ℕ, f^[m] s = t) is an equivalence relation on V, and for all s, t : V, if t is reachable from s, then there exists a return exponent k < Fintype.card V such that f^[k] t = s.
-/

/-- In a finite reversible transition system, reachability under f is an equivalence relation, and reverse paths exist with length strictly bounded by |V|. -/
theorem reversible_transition_reachability_equivalence {V : Type*} [Fintype V]
    (f : V → V) (hf : Function.Injective f) :
    Equivalence (fun s t : V => ∃ m : ℕ, f^[m] s = t) ∧
    ∀ s t : V, (∃ m : ℕ, f^[m] s = t) → ∃ k < Fintype.card V, f^[k] t = s := by
  open Function in
  have h_ret : ∀ s t : V, (∃ m : ℕ, f^[m] s = t) → ∃ k < Fintype.card V, f^[k] t = s := by
    intro s t ⟨m, hm⟩
    set p := minimalPeriod f s
    have hmem : s ∈ periodicPts f := Injective.mem_periodicPts hf s
    have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts hmem
    set k := (p - m % p) % p
    have hk_lt_p : k < p := Nat.mod_lt _ hp
    have hk_lt_card : k < Fintype.card V := lt_of_lt_of_le hk_lt_p minimalPeriod_le_card
    refine ⟨k, hk_lt_card, ?_⟩
    rw [← hm, ← iterate_add_apply]
    have hdvd : p ∣ k + m := by
      dsimp [k]
      rcases Nat.eq_zero_or_pos (m % p) with h0 | hpos
      · rw [h0]
        simp [Nat.dvd_of_mod_eq_zero h0]
      · have hlt : m % p < p := Nat.mod_lt m hp
        have h1 : p - m % p < p := by omega
        rw [Nat.mod_eq_of_lt h1]
        have : p - m % p + m = p * (m / p) + p := by
          have hm' : m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
          omega
        rw [this]
        exact dvd_add (dvd_mul_right p (m / p)) dvd_rfl
    exact isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd
  refine ⟨⟨?_, ?_, ?_⟩, h_ret⟩
  · intro s
    exact ⟨0, rfl⟩
  · intro s t hst
    obtain ⟨k, -, hk⟩ := h_ret s t hst
    exact ⟨k, hk⟩
  · intro s t u ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨n + m, ?_⟩
    rw [Function.iterate_add_apply, hm, hn]
