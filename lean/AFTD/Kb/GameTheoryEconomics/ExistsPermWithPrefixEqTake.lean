import AFTD.Prelude

/-!
# exists_perm_with_prefix_eq_take

Topic: social_choice   Node: 60560d175a33

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

Every duplicate-free list L of length m whose entries are the m candidates is the order of appearance of some permutation σ: for every k ≤ m the set {c | σ c < k} of candidates occupying the first k positions is exactly the set of the first k entries of L.
-/

/-- A duplicate-free list of all m candidates induces a permutation of the candidates whose every prefix set is the corresponding prefix of the list. -/
theorem exists_perm_with_prefix_eq_take {m : ℕ} (L : List (Fin m)) (hnd : L.Nodup) (hlen : L.length = m) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      Finset.univ.filter (fun c => (σ c : ℕ) < k) = (L.take k).toFinset := by
  have h_mem : ∀ c : Fin m, c ∈ L := by
    intro c
    have h1 : Finset.card L.toFinset = m := by
      rw [List.toFinset_card_of_nodup hnd, hlen]
    have h2 : L.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [h1, Fintype.card_fin]
    have h3 : c ∈ L.toFinset := by
      rw [h2]
      exact Finset.mem_univ c
    exact List.mem_toFinset.mp h3
  have h_idx_lt : ∀ c : Fin m, L.idxOf c < m := by
    intro c
    have h : L.idxOf c < L.length := List.idxOf_lt_length_iff.mpr (h_mem c)
    omega
  let f : Fin m → Fin m := fun c => ⟨L.idxOf c, h_idx_lt c⟩
  have hf_inj : Function.Injective f := by
    intro c1 c2 h
    have h_eq : (f c1).1 = (f c2).1 := congrArg Fin.val h
    dsimp [f] at h_eq
    exact (List.idxOf_inj (h_mem c1) (y := c2)).mp h_eq
  have hf_bij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective f hf_bij
  use σ
  intro k hk
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h_σ_val : (σ c : ℕ) = L.idxOf c := rfl
  rw [h_σ_val]
  rw [List.mem_toFinset]
  rw [List.mem_take_iff_idxOf_lt (h_mem c)]
