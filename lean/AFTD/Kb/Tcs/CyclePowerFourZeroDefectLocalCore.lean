import AFTD.Prelude

/-!
# cycle_power_four_zero_defect_local_core

Topic: combinatorics   Node: 95e0906b4545

Provenance: helper lemma. Defective half-model reduction for research thread RT-1.

For a span-four model, the endpoint-count and top-owner equations and distance-one coverage rule out a defect.
-/

theorem cycle_power_four_zero_defect_local_core
    (a b e : ℤ → Bool)
    (htop : ∀ v : ℤ, (b v).toNat + (a (v-1)).toNat + (e v).toNat = 1)
    (hcount : ∀ v : ℤ, (a (v-1)).toNat + (b (v-2)).toNat + (e v).toNat = 1)
    (hcover : ∀ v : ℤ, a v = true ∨ (a (v-1) = true ∧ b (v-1) = true) ∨ b (v-2) = true) :
    ∀ v : ℤ, e v = false := by
  have hper : ∀ v : ℤ, b v = b (v-2) := by
    intro v
    have heq : (b v).toNat = (b (v-2)).toNat := by
      have h₁ := htop v
      have h₂ := hcount v
      omega
    cases hv : b v <;> cases hw : b (v-2) <;> simp [hv, hw] at heq ⊢
  intro v
  by_contra hn
  have hev : e v = true := by
    cases h : e v with
    | false => exact (hn h).elim
    | true => rfl
  have hb : b v = false := by
    cases hv : b v with
    | false => rfl
    | true =>
      have h := htop v
      rw [hev, hv] at h
      simp only [Bool.toNat_true] at h
      omega
  have ha : a (v-1) = false := by
    cases hv : a (v-1) with
    | false => rfl
    | true =>
      have h := htop v
      rw [hev, hb, hv] at h
      simp only [Bool.toNat_true, Bool.toNat_false] at h
      omega
  have hb2 : b (v-2) = false := by rw [← hper v, hb]
  have hb3 : b (v-3) = true := by
    have hc := hcover (v-1)
    have h₁ : v-1-1 = v-2 := by ring
    have h₂ : v-1-2 = v-3 := by ring
    rw [h₁,h₂] at hc
    rcases hc with h | ⟨_,h⟩ | h
    · rw [ha] at h; contradiction
    · rw [hb2] at h; contradiction
    · exact h
  have hb1 : b (v-1) = true := by
    have h := hper (v-1)
    have hi : v-1-2 = v-3 := by ring
    rw [hi,hb3] at h
    exact h
  have hav : a v = true := by
    have hc := hcover v
    rcases hc with h | ⟨h,_⟩ | h
    · exact h
    · rw [ha] at h; contradiction
    · rw [hb2] at h; contradiction
  have hnext := htop (v+1)
  have hi : v+1-1 = v := by ring
  have hbnext : b (v+1) = true := by
    have h := hper (v+1)
    have hi : v+1-2 = v-1 := by ring
    rw [hi,hb1] at h
    exact h
  rw [hi,hbnext,hav] at hnext
  simp only [Bool.toNat_true] at hnext
  omega
