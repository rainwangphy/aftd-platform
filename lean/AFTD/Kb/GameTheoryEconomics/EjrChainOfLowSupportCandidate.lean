import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrGoodOfLowSupportCandidate
import AFTD.Kb.GameTheoryEconomics.EjrChainOfNestedCommittees
import AFTD.Kb.GameTheoryEconomics.EjrCommitteeUniv
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_chain_of_low_support_candidate

Topic: social_choice   Node: 1561ee48e0ff

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

If candidate c is approved by fewer than n/m voters and the profile with c deleted (transported along e) admits an EJR chain, then so does the original profile.
-/

def ejr_chain_of_low_support_candidate_f {m : ℕ} {c : Fin m}
    (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c}) (x : Fin (m - 1)) : Fin m := (e x).1

lemma ejr_chain_of_low_support_candidate_f_injective {m : ℕ} {c : Fin m}
    (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c}) :
    Function.Injective (ejr_chain_of_low_support_candidate_f e) := by
  intro x y h
  have : (e x) = (e y) := Subtype.ext h
  exact e.injective this

lemma ejr_chain_of_low_support_candidate_f_ne_c {m : ℕ} {c : Fin m}
    (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c}) (x : Fin (m - 1)) :
    ejr_chain_of_low_support_candidate_f e x ≠ c := (e x).2

lemma ejr_chain_of_low_support_candidate_f_surj_on {m : ℕ} {c : Fin m}
    (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c}) (y : Fin m) (hy : y ≠ c) :
    ∃ x, ejr_chain_of_low_support_candidate_f e x = y := by
  use e.symm ⟨y, hy⟩
  dsimp [ejr_chain_of_low_support_candidate_f]
  simp

lemma ejr_chain_of_low_support_candidate_card_preimage_eq {m : ℕ} {c : Fin m}
    (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c})
    (T : Finset (Fin m)) (hc : c ∉ T) :
    (Finset.univ.filter (fun x => ejr_chain_of_low_support_candidate_f e x ∈ T)).card = T.card := by
  have hinj : Function.Injective (ejr_chain_of_low_support_candidate_f e) :=
    ejr_chain_of_low_support_candidate_f_injective e
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    have hne : y ≠ c := by rintro rfl; exact hc hy
    obtain ⟨x, rfl⟩ := ejr_chain_of_low_support_candidate_f_surj_on e y hne
    exact ⟨x, hy, rfl⟩

lemma ejr_chain_of_low_support_candidate_subset_iff {n m : ℕ} (A : Fin n → Finset (Fin m)) {c : Fin m}
    (B : Fin n → Finset (Fin (m - 1))) (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c})
    (hB : ∀ (i : Fin n) (x : Fin (m - 1)), x ∈ B i ↔ (e x).1 ∈ A i)
    (i : Fin n) (T : Finset (Fin m)) (hc : c ∉ T) :
    T ⊆ A i ↔ (Finset.univ.filter (fun x => ejr_chain_of_low_support_candidate_f e x ∈ T)) ⊆ B i := by
  constructor
  · intro h x hx
    rw [Finset.mem_filter] at hx
    rw [hB i x]
    exact h hx.2
  · intro h y hy
    have hne : y ≠ c := by rintro rfl; exact hc hy
    obtain ⟨x, rfl⟩ := ejr_chain_of_low_support_candidate_f_surj_on e y hne
    have hx : x ∈ Finset.univ.filter (fun x => ejr_chain_of_low_support_candidate_f e x ∈ T) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hy⟩
    have := h hx
    rw [hB i x] at this
    exact this

lemma ejr_chain_of_low_support_candidate_inter_image_card {n m : ℕ} (A : Fin n → Finset (Fin m)) {c : Fin m}
    (B : Fin n → Finset (Fin (m - 1))) (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c})
    (hB : ∀ (i : Fin n) (x : Fin (m - 1)), x ∈ B i ↔ (e x).1 ∈ A i)
    (i : Fin n) (Q : Finset (Fin (m - 1))) :
    (A i ∩ Q.image (ejr_chain_of_low_support_candidate_f e)).card = (B i ∩ Q).card := by
  rw [← Finset.card_image_of_injective _ (ejr_chain_of_low_support_candidate_f_injective e)]
  congr 1
  ext y
  simp only [Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨hyA, x, hxQ, rfl⟩
    have hxB : x ∈ B i := (hB i x).mpr hyA
    exact ⟨x, ⟨hxB, hxQ⟩, rfl⟩
  · rintro ⟨x, ⟨hxB, hxQ⟩, rfl⟩
    have hyA : ejr_chain_of_low_support_candidate_f e x ∈ A i := (hB i x).mp hxB
    exact ⟨hyA, x, hxQ, rfl⟩

lemma ejr_chain_of_low_support_candidate_step_k (n m : ℕ) (A : Fin n → Finset (Fin m)) (hn : 0 < n)
    (c : Fin m) (hc : m * (Finset.univ.filter fun i => c ∈ A i).card < n)
    (B : Fin n → Finset (Fin (m - 1))) (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c})
    (hB : ∀ (i : Fin n) (x : Fin (m - 1)), x ∈ B i ↔ (e x).1 ∈ A i)
    (k : ℕ) (Q : Finset (Fin (m - 1))) (hejr : is_ejr_committee B k Q) :
    is_ejr_committee A k (Q.image (ejr_chain_of_low_support_candidate_f e)) := by
  have hejr_iff := (is_ejr_committee_iff_candidate_subsets B k Q).mp hejr
  have hcard_Q : Q.card = k := hejr_iff.1
  have hcard_P : (Q.image (ejr_chain_of_low_support_candidate_f e)).card = k := by
    rw [Finset.card_image_of_injective _ (ejr_chain_of_low_support_candidate_f_injective e), hcard_Q]
  have hcP : c ∉ Q.image (ejr_chain_of_low_support_candidate_f e) := by
    intro hcP
    rw [Finset.mem_image] at hcP
    obtain ⟨x, -, hx⟩ := hcP
    exact ejr_chain_of_low_support_candidate_f_ne_c e x hx
  apply ejr_good_of_low_support_candidate n m A hn c hc
    (Q.image (ejr_chain_of_low_support_candidate_f e)) hcP k hcard_P
  intro T hT_nonempty hcT
  set T' := Finset.univ.filter (fun x => ejr_chain_of_low_support_candidate_f e x ∈ T) with _hT'_def
  have hT'_card : T'.card = T.card := ejr_chain_of_low_support_candidate_card_preimage_eq e T hcT
  have hT'_nonempty : T'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty] at hT_nonempty ⊢
    intro h_empty
    have : T'.card = 0 := by rw [h_empty, Finset.card_empty]
    rw [hT'_card] at this
    rw [Finset.card_eq_zero] at this
    exact hT_nonempty this
  have h_bound := hejr_iff.2 T' hT'_nonempty
  have h_filter_eq :
      (Finset.univ.filter fun i =>
        T ⊆ A i ∧ (A i ∩ Q.image (ejr_chain_of_low_support_candidate_f e)).card < T.card) =
      (Finset.univ.filter fun i => T' ⊆ B i ∧ (B i ∩ Q).card < T'.card) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ejr_chain_of_low_support_candidate_subset_iff A B e hB i T hcT]
    rw [ejr_chain_of_low_support_candidate_inter_image_card A B e hB i Q]
    rw [hT'_card]
  rw [h_filter_eq, ← hT'_card]
  exact h_bound

/-- Chain-level form of deleting a low-support candidate: a chain for the reduced profile yields a chain for the original. -/
theorem ejr_chain_of_low_support_candidate (n m : ℕ) (A : Fin n → Finset (Fin m)) (hn : 0 < n)
    (c : Fin m) (hc : m * (Finset.univ.filter fun i => c ∈ A i).card < n)
    (B : Fin n → Finset (Fin (m - 1))) (e : Fin (m - 1) ≃ {x : Fin m // x ≠ c})
    (hB : ∀ (i : Fin n) (x : Fin (m - 1)), x ∈ B i ↔ (e x).1 ∈ A i)
    (hchain : ∃ σ' : Equiv.Perm (Fin (m - 1)), ∀ k, k ≤ m - 1 →
      is_ejr_committee B k (Finset.univ.filter fun x => (σ' x : ℕ) < k)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun x => (σ x : ℕ) < k) := by
  rcases hchain with ⟨σ', hσ'⟩
  apply ejr_chain_of_nested_committees A
  let Q : ℕ → Finset (Fin (m - 1)) := fun k => Finset.univ.filter fun x => (σ' x : ℕ) < k
  let W : ℕ → Finset (Fin m) := fun k =>
    if k < m then (Q k).image (ejr_chain_of_low_support_candidate_f e) else Finset.univ
  refine ⟨W, ?_, ?_, ?_⟩
  · have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le (c : ℕ)) c.is_lt
    have hW0 : W 0 = (Q 0).image (ejr_chain_of_low_support_candidate_f e) := if_pos hm
    rw [hW0]
    have hQ0 : Q 0 = ∅ := by
      ext x
      dsimp [Q]
      simp
    rw [hQ0, Finset.image_empty]
  · intro k hk
    dsimp [W]
    rw [if_pos hk]
    split_ifs with hk1
    · apply Finset.image_subset_image
      intro x hx
      dsimp [Q] at hx ⊢
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, Nat.lt_succ_of_lt hx.2⟩
    · exact Finset.subset_univ _
  · intro k hk
    dsimp [W]
    split_ifs with hkm
    · have hkle : k ≤ m - 1 := Nat.le_sub_one_of_lt hkm
      exact ejr_chain_of_low_support_candidate_step_k n m A hn c hc B e hB k (Q k) (hσ' k hkle)
    · have heq : k = m := Nat.le_antisymm hk (not_lt.mp hkm)
      subst heq
      exact ejr_committee_univ A hn
