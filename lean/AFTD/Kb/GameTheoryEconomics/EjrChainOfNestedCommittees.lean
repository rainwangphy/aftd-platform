import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.ExistsPermWithPrefixEqTake
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# ejr_chain_of_nested_committees

Topic: social_choice   Node: dcf95d662e4e

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

If there are committees W_0 ⊆ W_1 ⊆ ... ⊆ W_m with W_0 empty and W_k an EJR committee of size k for every k ≤ m, then there is a permutation of the candidates whose prefix of length k is exactly W_k, hence the target chain exists.
-/

/-- A nested family of EJR committees of sizes 0, 1, ..., m yields a permutation whose every prefix is the corresponding EJR committee. -/
theorem ejr_chain_of_nested_committees {n m : ℕ} (A : Fin n → Finset (Fin m)) :
    (∃ W : ℕ → Finset (Fin m), W 0 = ∅ ∧
        (∀ k, k < m → W k ⊆ W (k + 1)) ∧
        (∀ k, k ≤ m → is_ejr_committee A k (W k))) →
      ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
        is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k) := by
  rintro ⟨W, hW0, hmono, hEJR⟩
  have hcard : ∀ k, k ≤ m → (W k).card = k := fun k hk => (hEJR k hk).1
  have hdiff_card : ∀ k : Fin m, (W (k.1 + 1) \ W k.1).card = 1 := by
    intro k
    have hklt : (k : ℕ) < m := k.2
    have hsub : W k.1 ⊆ W (k.1 + 1) := hmono k.1 hklt
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    have h2 : (W k.1).card = k.1 := hcard k.1 (by omega)
    have h3 : (W (k.1 + 1)).card = k.1 + 1 := hcard (k.1 + 1) (by omega)
    omega
  let x : Fin m → Fin m := fun k => (Finset.card_eq_one.mp (hdiff_card k)).choose
  have hx : ∀ k : Fin m, W (k.1 + 1) \ W k.1 = {x k} :=
    fun k => (Finset.card_eq_one.mp (hdiff_card k)).choose_spec
  have hx_mem' : ∀ k : Fin m, x k ∈ W (k.1 + 1) := by
    intro k
    exact (Finset.mem_sdiff.mp (by rw [hx k]; exact Finset.mem_singleton_self (x k))).1
  have hx_not : ∀ k : Fin m, x k ∉ W k.1 := by
    intro k
    exact (Finset.mem_sdiff.mp (by rw [hx k]; exact Finset.mem_singleton_self (x k))).2
  have hmono' : ∀ a b, a ≤ b → b ≤ m → W a ⊆ W b := by
    intro a b hab hbm
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; exact Finset.Subset.refl _
    | succ b ih =>
      rcases lt_or_ge a (b + 1) with hlt | hge
      · exact (ih (by omega) (by omega)).trans (hmono b (by omega))
      · have : a = b + 1 := by omega
        subst this; exact Finset.Subset.refl _
  have hx_inj : Function.Injective x := by
    intro i j hij
    have hval : (i : ℕ) = (j : ℕ) := by
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
      · exfalso
        have h1 : x i ∈ W ((i:ℕ) + 1) := hx_mem' i
        have h2 : W ((i:ℕ) + 1) ⊆ W j.1 := hmono' _ _ (by omega) (le_of_lt j.2)
        have h3 : x j ∉ W j.1 := hx_not j
        exact h3 (hij ▸ h2 h1)
      · exact heq
      · exfalso
        have h1 : x j ∈ W ((j:ℕ) + 1) := hx_mem' j
        have h2 : W ((j:ℕ) + 1) ⊆ W i.1 := hmono' _ _ (by omega) (le_of_lt i.2)
        have h3 : x i ∉ W i.1 := hx_not i
        exact h3 (hij.symm ▸ h2 h1)
    exact Fin.ext hval
  let L : List (Fin m) := List.ofFn x
  have hlen : L.length = m := by simp [L]
  have hLnodup : L.Nodup := by
    show (List.ofFn x).Nodup
    rw [List.nodup_ofFn]
    exact hx_inj
  obtain ⟨σ, hσ⟩ := exists_perm_with_prefix_eq_take L hLnodup hlen
  have hprefix : ∀ k, k ≤ m → (L.take k).toFinset = W k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hW0]
    | succ k ih =>
      intro hk
      have hkm : k < m := hk
      have hk_le : k ≤ m := le_of_lt hkm
      have hk_lt_len : k < L.length := by rw [hlen]; exact hkm
      have hLk : L[k] = x ⟨k, hkm⟩ := by
        simp only [L, List.getElem_ofFn]
      have htake : (L.take (k + 1)).toFinset = (L.take k).toFinset ∪ {x ⟨k, hkm⟩} := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk_lt_len, Option.toList_some,
          List.toFinset_append, hLk]
        simp
      have hunion : W k ∪ {x ⟨k, hkm⟩} = W (k + 1) := by
        apply Finset.Subset.antisymm
        · intro a ha
          rcases Finset.mem_union.mp ha with h | h
          · exact hmono k hkm h
          · rw [Finset.mem_singleton] at h
            rw [h]
            have := hx_mem' ⟨k, hkm⟩
            simpa using this
        · intro a ha
          by_cases h : a ∈ W k
          · exact Finset.mem_union_left _ h
          · apply Finset.mem_union_right
            have hmem : a ∈ W (k + 1) \ W k := Finset.mem_sdiff.mpr ⟨ha, h⟩
            have hset := hx ⟨k, hkm⟩
            rw [hset] at hmem
            exact hmem
      rw [htake, ih hk_le, hunion]
  exact ⟨σ, fun k hk => by rw [hσ k hk, hprefix k hk]; exact hEJR k hk⟩
