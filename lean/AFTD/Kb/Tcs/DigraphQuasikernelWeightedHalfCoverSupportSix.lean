import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphKernelPerfectSubsetQuasikernelCover
import AFTD.Kb.Tcs.DigraphFourVerticesKernelPerfectTriple

/-!
# digraph_quasikernel_weighted_half_cover_support_six

Topic: graphs   Node: ec5e74fa22e0

Provenance: helper lemma. A small-support consequence of Lemma 14 of https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p53/pdf/; the finite local and weight inequalities were audited in experiment 14074.

For any finite loopless digraph and nonnegative integer vertex weights supported on at most six vertices, some quasi-kernel has at least half the total weight in its closed out-neighborhood.
-/

private lemma digraph_qkw_card_four_set {α : Type} [DecidableEq α] (a b c d : α)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    ({a,b,c,d} : Finset α).card = 4 := by
  rw [show ({a,b,c,d} : Finset α) = insert a (insert b (insert c ({d} : Finset α))) from rfl]
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]

private lemma digraph_qkw_weight_small_support
    {α : Type} [DecidableEq α] (P : Finset α) (w : α → ℕ) (h : P.card ≤ 3) :
    ∃ S : Finset α, S ⊆ P ∧ S.card ≤ 2 ∧ (∑ v ∈ P, w v) ≤ 2 * (∑ v ∈ S, w v) := by
  rcases Nat.lt_or_ge P.card 3 with h3 | h3
  · exact ⟨P, Finset.Subset.refl P, by omega, by omega⟩
  · have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x1, hx1, hx1max⟩ := Finset.exists_max_image P w hne
    have hcard1 : (P.erase x1).card = 2 := by rw [Finset.card_erase_of_mem hx1]; omega
    have hne1 : (P.erase x1).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hy⟩ := hne1
    have hyP : y ∈ P := Finset.mem_of_mem_erase hy
    have hyx : y ≠ x1 := (Finset.mem_erase.mp hy).1
    refine ⟨P.erase y, Finset.erase_subset y P, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hyP]; omega
    · have hx1mem : x1 ∈ P.erase y := Finset.mem_erase.mpr ⟨hyx.symm, hx1⟩
      have hle : w x1 ≤ ∑ v ∈ P.erase y, w v :=
        Finset.single_le_sum (f := w) (fun i _ => Nat.zero_le _) hx1mem
      have hsplit : ∑ v ∈ P, w v = w y + ∑ v ∈ P.erase y, w v :=
        (Finset.add_sum_erase P w hyP).symm
      have hxy : w y ≤ w x1 := hx1max y hyP
      omega

private lemma digraph_qkw_weight_four_bound
    {α : Type} [DecidableEq α] (P T : Finset α) (w : α → ℕ)
    (x1 x2 x3 x4 : α)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h34 : x3 ≠ x4)
    (hsub : ({x1, x2, x3, x4} : Finset α) ⊆ P)
    (hP6 : P.card ≤ 6)
    (hx1max : ∀ y ∈ P, w y ≤ w x1)
    (hx2max : ∀ y ∈ P, y ≠ x1 → w y ≤ w x2)
    (hx3max : ∀ y ∈ P, y ≠ x1 → y ≠ x2 → w y ≤ w x3)
    (hx4max : ∀ y ∈ P, y ≠ x1 → y ≠ x2 → y ≠ x3 → w y ≤ w x4)
    (hTsub : T ⊆ ({x1, x2, x3, x4} : Finset α))
    (hT3 : T.card = 3)
    (hx1T : x1 ∈ T) :
    ∑ v ∈ P, w v ≤ 2 * ∑ v ∈ T, w v := by
  have hA4 : ({x1,x2,x3,x4} : Finset α).card = 4 :=
    digraph_qkw_card_four_set x1 x2 x3 x4 h12 h13 h14 h23 h24 h34
  have hsumA : ∑ v ∈ ({x1,x2,x3,x4} : Finset α), w v = w x1 + w x2 + w x3 + w x4 := by
    rw [show ({x1,x2,x3,x4} : Finset α) = insert x1 (insert x2 (insert x3 ({x4} : Finset α))) from rfl]
    rw [Finset.sum_insert (by simp [h12, h13, h14]),
        Finset.sum_insert (by simp [h23, h24]),
        Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
    omega
  have hcard : (P \ ({x1,x2,x3,x4} : Finset α)).card ≤ 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hA4]
    omega
  have hbound_out : ∀ y ∈ P \ ({x1,x2,x3,x4} : Finset α), w y ≤ w x4 := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨hyP, hyA⟩ := hy
    have hy1 : y ≠ x1 := by intro h; exact hyA (h ▸ (by simp : x1 ∈ ({x1,x2,x3,x4} : Finset α)))
    have hy2 : y ≠ x2 := by intro h; exact hyA (h ▸ (by simp : x2 ∈ ({x1,x2,x3,x4} : Finset α)))
    have hy3 : y ≠ x3 := by intro h; exact hyA (h ▸ (by simp : x3 ∈ ({x1,x2,x3,x4} : Finset α)))
    exact hx4max y hyP hy1 hy2 hy3
  have hsumout : ∑ v ∈ P \ ({x1,x2,x3,x4} : Finset α), w v ≤ 2 * w x4 := by
    have h1 := Finset.sum_le_card_nsmul (P \ ({x1,x2,x3,x4} : Finset α)) w (w x4) hbound_out
    have h2 : (P \ ({x1,x2,x3,x4} : Finset α)).card * w x4 ≤ 2 * w x4 :=
      Nat.mul_le_mul_right (w x4) hcard
    calc ∑ v ∈ P \ ({x1,x2,x3,x4} : Finset α), w v
        ≤ (P \ ({x1,x2,x3,x4} : Finset α)).card • w x4 := h1
      _ = (P \ ({x1,x2,x3,x4} : Finset α)).card * w x4 := by simp
      _ ≤ 2 * w x4 := h2
  have hdiff1 : (({x1,x2,x3,x4} : Finset α) \ T).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub, hT3, hA4]
  obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hdiff1
  have hyA : y ∈ ({x1,x2,x3,x4} : Finset α) := by
    have hh : y ∈ ({x1,x2,x3,x4} : Finset α) \ T := by rw [hy_eq]; simp
    exact (Finset.mem_sdiff.mp hh).1
  have hyT : y ∉ T := by
    have hh : y ∈ ({x1,x2,x3,x4} : Finset α) \ T := by rw [hy_eq]; simp
    exact (Finset.mem_sdiff.mp hh).2
  have hyP : y ∈ P := hsub hyA
  have hy1 : y ≠ x1 := by intro h; exact hyT (h ▸ hx1T)
  have hwy : w y ≤ w x2 := hx2max y hyP hy1
  have hsumT : ∑ v ∈ ({x1,x2,x3,x4} : Finset α), w v = w y + ∑ v ∈ T, w v := by
    have h := Finset.sum_sdiff (f := w) hTsub
    rw [hy_eq, Finset.sum_singleton] at h
    omega
  have hsplit : ∑ v ∈ P, w v = ∑ v ∈ ({x1,x2,x3,x4} : Finset α), w v + ∑ v ∈ P \ ({x1,x2,x3,x4} : Finset α), w v := by
    have h := Finset.sum_sdiff (f := w) hsub
    omega
  have hx2le1 : w x2 ≤ w x1 := hx1max x2 (hsub (by simp))
  have hx4le3 : w x4 ≤ w x3 := hx3max x4 (hsub (by simp)) (Ne.symm h14) (Ne.symm h24)
  omega

private lemma digraph_qkw_kp_of_card_le_two
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (S : Finset α) (hS : S.card ≤ 2) :
    ∀ T ⊆ S, ∃ K ⊆ T,
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ T, ∃ u ∈ K, u = v ∨ D.Adj u v) := by
  intro T hT
  have hTcard : T.card ≤ 2 := le_trans (Finset.card_le_card hT) hS
  rcases Nat.lt_or_ge T.card 2 with h2 | h2
  · rcases Nat.lt_or_ge T.card 1 with h1 | h1
    · have h0 : T.card = 0 := by omega
      have hT0 : T = ∅ := Finset.card_eq_zero.mp h0
      refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · intro u hu; simp at hu
      · intro v hv; rw [hT0] at hv; simp at hv
    · have h1' : T.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1'
      refine ⟨{a}, ?_, ?_, ?_⟩
      · intro x hx; simpa [ha] using hx
      · intro u hu v hv huv
        rw [Finset.mem_singleton] at hu hv
        exact (huv (hu.trans hv.symm)).elim
      · intro v hv
        rw [ha, Finset.mem_singleton] at hv
        exact ⟨a, Finset.mem_singleton_self a, Or.inl hv.symm⟩
  · have h2' : T.card = 2 := by omega
    obtain ⟨a, b, hab, hT2⟩ := Finset.card_eq_two.mp h2'
    rw [hT2]
    by_cases habA : D.Adj a b
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; simp
      · intro u hu v hv huv
        rw [Finset.mem_singleton] at hu hv
        exact (huv (hu.trans hv.symm)).elim
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with hv | hv
        · exact ⟨a, Finset.mem_singleton_self a, Or.inl hv.symm⟩
        · refine ⟨a, Finset.mem_singleton_self a, Or.inr ?_⟩
          rw [hv]; exact habA
    · by_cases hbaA : D.Adj b a
      · refine ⟨{b}, ?_, ?_, ?_⟩
        · intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; simp
        · intro u hu v hv huv
          rw [Finset.mem_singleton] at hu hv
          exact (huv (hu.trans hv.symm)).elim
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with hv | hv
          · refine ⟨b, Finset.mem_singleton_self b, Or.inr ?_⟩
            rw [hv]; exact hbaA
          · exact ⟨b, Finset.mem_singleton_self b, Or.inl hv.symm⟩
      · refine ⟨{a, b}, ?_, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          tauto
        · intro u hu v hv huv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact (huv (hu.trans hv.symm)).elim
          · rw [hu, hv]; exact habA
          · rw [hu, hv]; exact hbaA
          · exact (huv (hu.trans hv.symm)).elim
        · intro v hv
          exact ⟨v, hv, Or.inl rfl⟩

theorem digraph_quasikernel_weighted_half_cover_support_six
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (w : α → ℕ)
    (hsupport : (Finset.univ.filter (fun v => w v ≠ 0)).card ≤ 6) :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ z, D.Adj u z ∧ D.Adj z v) ∧
      (∑ v ∈ Finset.univ, w v) ≤
        2 * (∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v) := by
  classical
  set P : Finset α := Finset.univ.filter (fun v => w v ≠ 0) with hP
  have hPcard : P.card ≤ 6 := hsupport
  have hsumP : (∑ v ∈ P, w v) = ∑ v ∈ Finset.univ, w v := by
    refine Finset.sum_subset (Finset.subset_univ P) ?_
    intro x _ hx
    have hx' : ¬ (w x ≠ 0) := by
      intro h
      exact hx (by rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simpa using hx'
  rcases Nat.lt_or_ge P.card 4 with hlt | hge
  · have hsmall : P.card ≤ 3 := by omega
    obtain ⟨S, hSP, hScard, hSweight⟩ := digraph_qkw_weight_small_support P w hsmall
    have hkp := digraph_qkw_kp_of_card_le_two D hloop S hScard
    obtain ⟨Q, hQind, hQcover, hQS, hQout⟩ := digraph_kernel_perfect_subset_quasikernel_cover D S hkp
    refine ⟨Q, hQind, hQcover, ?_⟩
    have hSN : S ⊆ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v) := by
      intro s hs
      obtain ⟨q, hqQ, hq⟩ := hQS s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hqQ, hq⟩
    have hsumN : ∑ v ∈ S, w v ≤ ∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v :=
      Finset.sum_le_sum_of_subset_of_nonneg hSN (fun i _ _ => Nat.zero_le _)
    calc ∑ v ∈ Finset.univ, w v = ∑ v ∈ P, w v := hsumP.symm
      _ ≤ 2 * ∑ v ∈ S, w v := hSweight
      _ ≤ 2 * ∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v :=
          Nat.mul_le_mul_left 2 hsumN
  · have h4 : 4 ≤ P.card := hge
    obtain ⟨x1, hx1P, hx1max⟩ := Finset.exists_max_image P w (Finset.card_pos.mp (by omega))
    have hc1 : (P.erase x1).card = P.card - 1 := Finset.card_erase_of_mem hx1P
    have hne1 : (P.erase x1).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x2, hx2e, hx2max⟩ := Finset.exists_max_image (P.erase x1) w hne1
    have hx2P : x2 ∈ P := Finset.mem_of_mem_erase hx2e
    have hx2ne : x2 ≠ x1 := (Finset.mem_erase.mp hx2e).1
    have hc2 : ((P.erase x1).erase x2).card = P.card - 2 := by
      rw [Finset.card_erase_of_mem hx2e, hc1]; omega
    have hne2 : ((P.erase x1).erase x2).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x3, hx3e, hx3max⟩ := Finset.exists_max_image ((P.erase x1).erase x2) w hne2
    have hx3P : x3 ∈ P := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx3e)
    have hx3ne1 : x3 ≠ x1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx3e)).1
    have hx3ne2 : x3 ≠ x2 := (Finset.mem_erase.mp hx3e).1
    have hc3 : (((P.erase x1).erase x2).erase x3).card = P.card - 3 := by
      rw [Finset.card_erase_of_mem hx3e, hc2]; omega
    have hne3 : (((P.erase x1).erase x2).erase x3).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x4, hx4e, hx4max⟩ := Finset.exists_max_image (((P.erase x1).erase x2).erase x3) w hne3
    have hx4e' : x4 ∈ (P.erase x1).erase x2 := (Finset.mem_erase.mp hx4e).2
    have hx4ne3 : x4 ≠ x3 := (Finset.mem_erase.mp hx4e).1
    have hx4ne2 : x4 ≠ x2 := (Finset.mem_erase.mp hx4e').1
    have hx4e'' : x4 ∈ P.erase x1 := (Finset.mem_erase.mp hx4e').2
    have hx4ne1 : x4 ≠ x1 := (Finset.mem_erase.mp hx4e'').1
    have hx4P : x4 ∈ P := Finset.mem_of_mem_erase hx4e''
    have h12 : x1 ≠ x2 := hx2ne.symm
    have h13 : x1 ≠ x3 := hx3ne1.symm
    have h14 : x1 ≠ x4 := hx4ne1.symm
    have h23 : x2 ≠ x3 := hx3ne2.symm
    have h24 : x2 ≠ x4 := hx4ne2.symm
    have h34 : x3 ≠ x4 := hx4ne3.symm
    have hsub : ({x1,x2,x3,x4} : Finset α) ⊆ P := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hx1P
      · exact hx2P
      · exact hx3P
      · exact hx4P
    have hAcard : ({x1,x2,x3,x4} : Finset α).card = 4 :=
      digraph_qkw_card_four_set x1 x2 x3 x4 h12 h13 h14 h23 h24 h34
    have hx1A : x1 ∈ ({x1,x2,x3,x4} : Finset α) := by simp
    obtain ⟨T, hTA, hx1T, hTcard, hTkp⟩ :=
      digraph_four_vertices_kernel_perfect_triple D hloop ({x1,x2,x3,x4} : Finset α) hAcard x1 hx1A
    obtain ⟨Q, hQind, hQcover, hQT, hQout⟩ := digraph_kernel_perfect_subset_quasikernel_cover D T hTkp
    refine ⟨Q, hQind, hQcover, ?_⟩
    have hx2maxP : ∀ y ∈ P, y ≠ x1 → w y ≤ w x2 := by
      intro y hyP hyne
      exact hx2max y (Finset.mem_erase.mpr ⟨hyne, hyP⟩)
    have hx3maxP : ∀ y ∈ P, y ≠ x1 → y ≠ x2 → w y ≤ w x3 := by
      intro y hyP hy1 hy2
      exact hx3max y (Finset.mem_erase.mpr ⟨hy2, Finset.mem_erase.mpr ⟨hy1, hyP⟩⟩)
    have hx4maxP : ∀ y ∈ P, y ≠ x1 → y ≠ x2 → y ≠ x3 → w y ≤ w x4 := by
      intro y hyP hy1 hy2 hy3
      exact hx4max y (Finset.mem_erase.mpr ⟨hy3, Finset.mem_erase.mpr ⟨hy2, Finset.mem_erase.mpr ⟨hy1, hyP⟩⟩⟩)
    have hweight := digraph_qkw_weight_four_bound P T w x1 x2 x3 x4 h12 h13 h14 h23 h24 h34
      hsub hPcard hx1max hx2maxP hx3maxP hx4maxP hTA hTcard hx1T
    have hTN : T ⊆ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v) := by
      intro s hs
      obtain ⟨q, hqQ, hq⟩ := hQT s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hqQ, hq⟩
    have hsumN : ∑ v ∈ T, w v ≤ ∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v :=
      Finset.sum_le_sum_of_subset_of_nonneg hTN (fun i _ _ => Nat.zero_le _)
    calc ∑ v ∈ Finset.univ, w v = ∑ v ∈ P, w v := hsumP.symm
      _ ≤ 2 * ∑ v ∈ T, w v := hweight
      _ ≤ 2 * ∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v :=
          Nat.mul_le_mul_left 2 hsumN
