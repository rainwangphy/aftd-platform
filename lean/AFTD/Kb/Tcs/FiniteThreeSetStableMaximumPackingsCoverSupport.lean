import AFTD.Prelude

/-!
# finite_three_set_stable_maximum_packings_cover_support

Topic: graphs   Node: 133a0d301d3c

Provenance: helper lemma. Elementary packing exchange for the triangle packing-cover campaign, related to arXiv:2610.15539, Section 1.

For a finite family of three-element sets, suppose every packing has at most k members and, for each point occurring in the family, some k-member packing omits that point. Then every point occurring in the family is covered by some k-member packing.
-/

theorem finite_three_set_stable_maximum_packings_cover_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ)
    (hthree : ∀ t ∈ F, t.card = 3)
    (hmax : ∀ P : Finset (Finset α), P ⊆ F →
      (P : Set (Finset α)).Pairwise Disjoint → P.card ≤ k)
    (hstable : ∀ y ∈ F.biUnion id, ∃ P : Finset (Finset α),
      P ⊆ F ∧ (P : Set (Finset α)).Pairwise Disjoint ∧ P.card = k ∧
      ∀ s ∈ P, y ∉ s) :
    ∀ x ∈ F.biUnion id, ∃ P : Finset (Finset α),
      P ⊆ F ∧ (P : Set (Finset α)).Pairwise Disjoint ∧ P.card = k ∧
      ∃ s ∈ P, x ∈ s := by
  classical
  intro x hx
  obtain ⟨T, hTF, hxT⟩ := Finset.mem_biUnion.mp hx
  change x ∈ T at hxT
  have herase : (T.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxT, hthree T hTF]
  obtain ⟨y, z, hyz, hyzT⟩ := Finset.card_eq_two.mp herase
  have hTx : T = {x, y, z} := by
    have hh := Finset.insert_erase hxT
    rw [hyzT] at hh
    simpa using hh.symm
  have hyT : y ∈ T := by rw [hTx]; simp
  have hzT : z ∈ T := by rw [hTx]; simp
  by_contra hfail
  have hyF : y ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨T, hTF, hyT⟩
  obtain ⟨P, hPF, hPd, hPk, hPy⟩ := hstable y hyF
  have hPx : ∀ s ∈ P, x ∉ s := by
    intro s hs hxs
    exact hfail ⟨P, hPF, hPd, hPk, s, hs, hxs⟩
  have hdisT : ∀ s ∈ P, z ∉ s → Disjoint T s := by
    intro s hs hzs
    apply Finset.disjoint_left.mpr
    intro a ha has
    rw [hTx] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hPx s hs has
    · exact hPy s hs has
    · exact hzs has
  have hrex : ∃ r ∈ P, z ∈ r := by
    by_contra hno
    have hnoz : ∀ s ∈ P, z ∉ s := by simpa using hno
    have hnot : T ∉ P := by
      intro hTP
      exact hPx T hTP hxT
    have hsub : insert T P ⊆ F := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hTF
      · exact hPF hs
    have hpair : ((insert T P : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint := by
      intro s hs t ht hne
      simp only [Finset.mem_coe, Finset.mem_insert] at hs ht
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · exact (hne rfl).elim
      · exact hdisT t ht (hnoz t ht)
      · exact (hdisT s hs (hnoz s hs)).symm
      · exact hPd hs ht hne
    have hc := hmax (insert T P) hsub hpair
    rw [Finset.card_insert_of_notMem hnot, hPk] at hc
    omega
  obtain ⟨r, hrP, hzr⟩ := hrex
  have hnot : T ∉ P := by
    intro hTP
    exact hPx T hTP hxT
  have hrest : ∀ s ∈ P.erase r, Disjoint T s := by
    intro s hs
    have hsP := (Finset.mem_erase.mp hs).2
    have hsr := (Finset.mem_erase.mp hs).1
    apply hdisT s hsP
    intro hzs
    have hd := hPd hsP hrP hsr
    exact (Finset.disjoint_left.mp hd) hzs hzr
  let Q : Finset (Finset α) := insert T (P.erase r)
  have hQF : Q ⊆ F := by
    intro s hs
    simp only [Q, Finset.mem_insert, Finset.mem_erase] at hs
    rcases hs with rfl | ⟨_, hs⟩
    · exact hTF
    · exact hPF hs
  have hQd : (Q : Set (Finset α)).Pairwise Disjoint := by
    intro s hs t ht hne
    simp only [Q, Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hs ht
    rcases hs with rfl | ⟨hsr, hs⟩ <;> rcases ht with rfl | ⟨htr, ht⟩
    · exact (hne rfl).elim
    · exact hrest t (Finset.mem_erase.mpr ⟨htr, ht⟩)
    · exact (hrest s (Finset.mem_erase.mpr ⟨hsr, hs⟩)).symm
    · exact hPd hs ht hne
  have hQk : Q.card = k := by
    change (insert T (P.erase r)).card = k
    rw [Finset.card_insert_of_notMem (fun h => hnot (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hrP, hPk]
    have : 0 < k := by rw [← hPk]; exact Finset.card_pos.mpr ⟨r, hrP⟩
    omega
  exact hfail ⟨Q, hQF, hQd, hQk, T, Finset.mem_insert_self _ _, hxT⟩
