import AFTD.Prelude

/-!
# five_odd_mixed_witness_incidence_impossible

Topic: graphs   Node: 959b08708a04

Provenance: helper lemma. OP-1957: general mixed forced-witness incidence reduction in the saturated five-by-odd boundary.

For a four-element first set and an opposite set C of any size at least seven, the displayed row, column and separator budgets prevent the four listed large- and small-witness patterns from covering all vertices of C other than p and q.
-/

set_option maxHeartbeats 3000000

lemma in1158_incidence_card_bound {V : Type*} [DecidableEq V]
    (A C L : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hA : A.card = 4) (hLC : L ⊆ C)
    (hrow : ∀ a ∈ A, (C.filter (R a)).card ≤ 2)
    (d : ℕ) (hcol : ∀ y ∈ L, d ≤ (A.filter (fun a => R a y)).card) :
    d * L.card ≤ 8 := by
  classical
  have hl : (∑ y ∈ L, d) ≤ ∑ y ∈ L, (A.filter (fun a => R a y)).card :=
    Finset.sum_le_sum hcol
  have hu : (∑ a ∈ A, (L.filter (R a)).card) ≤ ∑ a ∈ A, (2:ℕ) := by
    apply Finset.sum_le_sum
    intro a ha
    have hs : L.filter (R a) ⊆ C.filter (R a) := Finset.filter_subset_filter _ hLC
    exact (Finset.card_le_card hs).trans (hrow a ha)
  have heq : (∑ y ∈ L, (A.filter (fun a => R a y)).card) =
      ∑ a ∈ A, (L.filter (R a)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hl' : d * L.card ≤ ∑ y ∈ L, (A.filter (fun a => R a y)).card := by
    simpa [mul_comm] using hl
  have hu' : (∑ a ∈ A, (L.filter (R a)).card) ≤ 8 := by
    simpa [hA] using hu
  omega

lemma in1158_saturated_two_sets {V : Type*} [DecidableEq V]
    (U B Z D : Finset V) (c r : ℕ) (hc : 7 ≤ c)
    (hU : U ⊆ B) (hZ : Z ⊆ D) (hsize : U.card + Z.card = c-4)
    (hbudget : r + B.card + D.card + 1 ≤ c-3) :
    r=0 ∧ U=B ∧ Z=D := by
  have hUB := Finset.card_le_card hU
  have hZD := Finset.card_le_card hZ
  have hr : r=0 := by omega
  have hUB' : B.card ≤ U.card := by omega
  have hZD' : D.card ≤ Z.card := by omega
  exact ⟨hr, Finset.eq_of_subset_of_card_le hU hUB', Finset.eq_of_subset_of_card_le hZ hZD'⟩

theorem five_odd_mixed_witness_incidence_impossible
    {V : Type*} [DecidableEq V] (A B C : Finset V)
    (R S T : V → V → Prop) [DecidableRel R] [DecidableRel S] [DecidableRel T]
    (hA : A.card=4) (hC : 7 ≤ C.card) (p q : V) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hTsymm : ∀ u v, T u v → T v u)
    (hArow : ∀ a ∈ A, (C.filter (R a)).card ≤ 2)
    (hCbudget : ∀ c ∈ C,
      (A.filter (fun a => R a c)).card + (B.filter (fun b => S b c)).card +
      ((C.erase c).filter (T c)).card + (if c=p ∨ c=q then 1 else 0) ≤ C.card-3)
    (hcut : ∀ U ⊆ B, ∀ W ⊆ C, U.Nonempty → W.Nonempty →
      (∀ b ∈ U, ∀ c ∈ W, S b c) → U.card+W.card ≤ C.card)
    (hpatterns : ∀ y ∈ C \ {p,q},
      (∃ r ∈ ({p,q} : Finset V), ∃ U ⊆ A, U.card=2 ∧ ∀ a ∈ U, R a y ∧ R a r) ∨
      (∀ a ∈ A, R a y) ∨
      (¬ T p q ∧ (¬ T y p ∨ ¬ T y q) ∧
        ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=C.card-4 ∧
          (∀ b ∈ U, S b p ∧ S b q ∧ S b y) ∧
          (∀ z ∈ Z, T z p ∧ T z q ∧ T z y)) ∨
      (T p q ∧ T y p ∧ T y q)) : False := by
  classical
  let Y : Finset V := C \ {p,q}
  let Large : V → Prop := fun y =>
    (∃ r ∈ ({p,q} : Finset V), ∃ U ⊆ A, U.card=2 ∧ ∀ a ∈ U, R a y ∧ R a r) ∨
    (∀ a ∈ A, R a y)
  let L : Finset V := Y.filter Large
  let W : Finset V := Y \ L
  have hpair : ({p,q} : Finset V) ⊆ C := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact hp
    · exact hq
  have hYcard : Y.card+2=C.card := by
    dsimp only [Y]
    rw [Finset.card_sdiff_of_subset hpair]
    have hpqcard : ({p,q} : Finset V).card=2 := by simp [hpq]
    rw [hpqcard]
    have := Finset.card_le_card hpair
    rw [hpqcard] at this
    omega
  have hLY : L ⊆ Y := Finset.filter_subset _ _
  have hYC : Y ⊆ C := Finset.sdiff_subset
  have hLC : L ⊆ C := hLY.trans hYC
  have hWcard : W.card+L.card=Y.card := by
    dsimp only [W]
    rw [Finset.card_sdiff_of_subset hLY]
    have := Finset.card_le_card hLY
    omega
  have hWsub : W ⊆ Y := Finset.sdiff_subset
  have hWnotp : p ∉ W := by
    intro h
    have hy := hWsub h
    simp [Y] at hy
  have hWnotq : q ∉ W := by
    intro h
    have hy := hWsub h
    simp [Y] at hy
  have hLcol : ∀ y ∈ L, 2 ≤ (A.filter (fun a => R a y)).card := by
    intro y hy
    have hlarge : Large y := (Finset.mem_filter.mp hy).2
    rcases hlarge with ⟨r,hr,U,hUA,hcard,hR⟩ | hall
    · have hsub : U ⊆ A.filter (fun a => R a y) := by
        intro a ha
        exact Finset.mem_filter.mpr ⟨hUA ha,(hR a ha).1⟩
      have hh := Finset.card_le_card hsub
      omega
    · have hfil : A.filter (fun a => R a y) = A := Finset.filter_eq_self.mpr hall
      rw [hfil,hA]
      omega
  have hLcard : L.card ≤ 4 := by
    have hh := in1158_incidence_card_bound A C L R hA hLC hArow 2 hLcol
    omega
  have hWlower : C.card-6 ≤ W.card := by omega
  have hWnonempty : W.Nonempty := Finset.card_pos.mp (by omega)
  have hWmem : ∀ y ∈ W, y ∈ C ∧ y ≠ p ∧ y ≠ q := by
    intro y hy
    have h := Finset.mem_sdiff.mp (hWsub hy)
    have hn : y ≠ p ∧ y ≠ q := by simpa using h.2
    exact ⟨h.1,hn⟩
  have hWpattern : ∀ y ∈ W,
      (¬ T p q ∧ (¬ T y p ∨ ¬ T y q) ∧
        ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=C.card-4 ∧
          (∀ b ∈ U, S b p ∧ S b q ∧ S b y) ∧
          (∀ z ∈ Z, T z p ∧ T z q ∧ T z y)) ∨
      (T p q ∧ T y p ∧ T y q) := by
    intro y hy
    have hyY : y ∈ Y := hWsub hy
    have hnL : y ∉ L := (Finset.mem_sdiff.mp hy).2
    have hnlarge : ¬ Large y := by
      intro hh
      exact hnL (Finset.mem_filter.mpr ⟨hyY,hh⟩)
    have ht := hpatterns y hyY
    rcases ht with h1 | h2 | h3 | h4
    · exact False.elim (hnlarge (Or.inl h1))
    · exact False.elim (hnlarge (Or.inr h2))
    · exact Or.inl h3
    · exact Or.inr h4
  by_cases hT : T p q
  · have hWp : ∀ y ∈ W, T p y := by
      intro y hy
      rcases hWpattern y hy with h3|h4
      · exact False.elim (h3.1 hT)
      · exact hTsymm _ _ h4.2.1
    have hWq : ∀ y ∈ W, T q y := by
      intro y hy
      rcases hWpattern y hy with h3|h4
      · exact False.elim (h3.1 hT)
      · exact hTsymm _ _ h4.2.2
    have hpSet : insert q W ⊆ (C.erase p).filter (T p) := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq.symm,hq⟩,hT⟩
      · have hm := hWmem y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hm.2.1,hm.1⟩,hWp y hy⟩
    have hqSet : insert p W ⊆ (C.erase q).filter (T q) := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq,hp⟩,hTsymm _ _ hT⟩
      · have hm := hWmem y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hm.2.2,hm.1⟩,hWq y hy⟩
    have hpTcard : W.card+1 ≤ ((C.erase p).filter (T p)).card := by
      have hh := Finset.card_le_card hpSet
      simpa [hWnotq] using hh
    have hqTcard : W.card+1 ≤ ((C.erase q).filter (T q)).card := by
      have hh := Finset.card_le_card hqSet
      simpa [hWnotp] using hh
    have hpR : (A.filter (fun a => R a p)).card ≤ 1 := by
      have hh := hCbudget p hp
      simp only [true_or,if_true] at hh
      omega
    have hqR : (A.filter (fun a => R a q)).card ≤ 1 := by
      have hh := hCbudget q hq
      simp only [or_true,if_true] at hh
      omega
    have hWupper : W.card ≤ C.card-5 := by
      have hh := hCbudget p hp
      simp only [true_or,if_true] at hh
      omega
    have hpqR : ∀ r ∈ ({p,q} : Finset V), (A.filter (fun a => R a r)).card ≤ 1 := by
      intro r hr
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl|rfl
      · exact hpR
      · exact hqR
    have hLall : ∀ y ∈ L, ∀ a ∈ A, R a y := by
      intro y hy
      have hlarge := (Finset.mem_filter.mp hy).2
      rcases hlarge with ⟨r,hr,U,hUA,hcard,hR⟩ | hall
      · have hsub : U ⊆ A.filter (fun a => R a r) := by
          intro a ha
          exact Finset.mem_filter.mpr ⟨hUA ha,(hR a ha).2⟩
        have h1 := Finset.card_le_card hsub
        have h2 := hpqR r hr
        omega
      · exact hall
    have hL4 : ∀ y ∈ L, 4 ≤ (A.filter (fun a => R a y)).card := by
      intro y hy
      have hfil : A.filter (fun a => R a y) = A := Finset.filter_eq_self.mpr (hLall y hy)
      rw [hfil,hA]
    have hLtwo : L.card ≤ 2 := by
      have hh := in1158_incidence_card_bound A C L R hA hLC hArow 4 hL4
      omega
    omega
  · let Bp : Finset V := B.filter (fun b => S b p)
    let Dp : Finset V := (C.erase p).filter (T p)
    let Bq : Finset V := B.filter (fun b => S b q)
    let Dq : Finset V := (C.erase q).filter (T q)
    have hsaturation : ∀ y ∈ W,
        ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=C.card-4 ∧
          (∀ b ∈ U, S b p ∧ S b q ∧ S b y) ∧
          (∀ z ∈ Z, T z p ∧ T z q ∧ T z y) ∧
          U=Bp ∧ Z=Dp ∧
          (A.filter (fun a => R a p)).card=0 ∧ (A.filter (fun a => R a q)).card=0 := by
      intro y hy
      rcases hWpattern y hy with hsmall|hsmall
      · rcases hsmall with ⟨_,_,U,hUB,Z,hZ,hsize,hSU,hTZ⟩
        have hUBp : U ⊆ Bp := by
          intro b hb
          exact Finset.mem_filter.mpr ⟨hUB hb,(hSU b hb).1⟩
        have hUBq : U ⊆ Bq := by
          intro b hb
          exact Finset.mem_filter.mpr ⟨hUB hb,(hSU b hb).2.1⟩
        have hZp : Z ⊆ Dp := by
          intro z hz
          have hz0 := Finset.mem_sdiff.mp (hZ hz)
          have hzn : z ≠ p := by
            intro he
            apply hz0.2
            simp [he]
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzn,hz0.1⟩,
            hTsymm _ _ (hTZ z hz).1⟩
        have hZq : Z ⊆ Dq := by
          intro z hz
          have hz0 := Finset.mem_sdiff.mp (hZ hz)
          have hzn : z ≠ q := by
            intro he
            apply hz0.2
            simp [he]
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzn,hz0.1⟩,
            hTsymm _ _ (hTZ z hz).2.1⟩
        have hbp : (A.filter (fun a => R a p)).card + Bp.card + Dp.card + 1 ≤ C.card-3 := by
          have hh := hCbudget p hp
          simpa only [true_or,if_true] using hh
        have hbq : (A.filter (fun a => R a q)).card + Bq.card + Dq.card + 1 ≤ C.card-3 := by
          have hh := hCbudget q hq
          simpa only [or_true,if_true] using hh
        have hpSat := in1158_saturated_two_sets U Bp Z Dp C.card
          (A.filter (fun a => R a p)).card hC hUBp hZp hsize hbp
        have hqSat := in1158_saturated_two_sets U Bq Z Dq C.card
          (A.filter (fun a => R a q)).card hC hUBq hZq hsize hbq
        exact ⟨U,hUB,Z,hZ,hsize,hSU,hTZ,hpSat.2.1,hpSat.2.2,hpSat.1,hqSat.1⟩
      · exact False.elim (hT hsmall.1)
    obtain ⟨y0,hy0⟩ := hWnonempty
    obtain ⟨U0,hU0,Z0,hZ0,hsize0,hSU0,hTZ0,hUeq0,hZeq0,hRp0,hRq0⟩ := hsaturation y0 hy0
    have hpqR : ∀ r ∈ ({p,q} : Finset V), (A.filter (fun a => R a r)).card = 0 := by
      intro r hr
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl|rfl
      · exact hRp0
      · exact hRq0
    have hLall : ∀ y ∈ L, ∀ a ∈ A, R a y := by
      intro y hy
      have hlarge := (Finset.mem_filter.mp hy).2
      rcases hlarge with ⟨r,hr,U,hUA,hcard,hR⟩ | hall
      · have hsub : U ⊆ A.filter (fun a => R a r) := by
          intro a ha
          exact Finset.mem_filter.mpr ⟨hUA ha,(hR a ha).2⟩
        have h1 := Finset.card_le_card hsub
        have h2 := hpqR r hr
        omega
      · exact hall
    have hL4 : ∀ y ∈ L, 4 ≤ (A.filter (fun a => R a y)).card := by
      intro y hy
      have hfil : A.filter (fun a => R a y) = A := Finset.filter_eq_self.mpr (hLall y hy)
      rw [hfil,hA]
    have hLtwo : L.card ≤ 2 := by
      have hh := in1158_incidence_card_bound A C L R hA hLC hArow 4 hL4
      omega
    have hWlower' : C.card-4 ≤ W.card := by omega
    have hDempty : Dp = ∅ := by
      by_contra hne
      obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hzZ0 : z ∈ Z0 := by rw [hZeq0]; exact hz
      have hzsrc := Finset.mem_sdiff.mp (hZ0 hzZ0)
      have hznp : z ≠ p := by
        intro he
        apply hzsrc.2
        simp [he]
      have hznq : z ≠ q := by
        intro he
        apply hzsrc.2
        simp [he]
      have hzY : z ∈ Y := by
        apply Finset.mem_sdiff.mpr
        exact ⟨hzsrc.1, by simpa [hznp,hznq]⟩
      have hznW : z ∉ W := by
        intro hzW
        obtain ⟨Uz,hUz,Zz,hZz,hsz,hSUz,hTZz,hUeqz,hZeqz,hRpz,hRqz⟩ := hsaturation z hzW
        have hzZz : z ∈ Zz := by rw [hZeqz]; exact hz
        have hh := Finset.mem_sdiff.mp (hZz hzZz)
        apply hh.2
        simp
      have hzL : z ∈ L := by
        by_contra hn
        exact hznW (Finset.mem_sdiff.mpr ⟨hzY,hn⟩)
      have hzR : (A.filter (fun a => R a z)).card=4 := by
        have hfil : A.filter (fun a => R a z) = A := Finset.filter_eq_self.mpr (hLall z hzL)
        rw [hfil,hA]
      have hzWp : ∀ y ∈ W, T z y := by
        intro y hy
        obtain ⟨Uy,hUy,Zy,hZy,hsz,hSUy,hTZy,hUeqy,hZeqy,hRpy,hRqy⟩ := hsaturation y hy
        have hzZy : z ∈ Zy := by rw [hZeqy]; exact hz
        exact (hTZy z hzZy).2.2
      have hzSet : insert p (insert q W) ⊆ (C.erase z).filter (T z) := by
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl|rfl|hy
        · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hznp.symm,hp⟩,(hTZ0 z hzZ0).1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hznq.symm,hq⟩,(hTZ0 z hzZ0).2.1⟩
        · have hm := hWmem y hy
          have hyz : y ≠ z := by intro he; subst y; exact hznW hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hyz,hm.1⟩,hzWp y hy⟩
      have hzTcard : W.card+2 ≤ ((C.erase z).filter (T z)).card := by
        have hh := Finset.card_le_card hzSet
        have hh' : W.card+1 < ((C.erase z).filter (T z)).card := by
          simpa [hWnotp,hWnotq,hpq,hpq.symm] using hh
        omega
      have hbz := hCbudget z hzsrc.1
      omega
    have hBpCard : Bp.card = C.card-4 := by
      rw [hUeq0,hZeq0,hDempty] at hsize0
      simpa using hsize0
    have hBpSub : Bp ⊆ B := Finset.filter_subset _ _
    have hBpNonempty : Bp.Nonempty := Finset.card_pos.mp (by omega)
    let Q : Finset V := insert p (insert q W)
    have hQsub : Q ⊆ C := by
      intro y hy
      simp only [Q,Finset.mem_insert] at hy
      rcases hy with rfl|rfl|hy
      · exact hp
      · exact hq
      · exact (hWmem y hy).1
    have hQnonempty : Q.Nonempty := by exact ⟨p,Finset.mem_insert_self _ _⟩
    have hcross : ∀ b ∈ Bp, ∀ y ∈ Q, S b y := by
      intro b hb y hy
      simp only [Q,Finset.mem_insert] at hy
      rcases hy with rfl|rfl|hy
      · exact (Finset.mem_filter.mp hb).2
      · have hb0 : b ∈ U0 := by rw [hUeq0]; exact hb
        exact (hSU0 b hb0).2.1
      · obtain ⟨Uy,hUy,Zy,hZy,hsz,hSUy,hTZy,hUeqy,hZeqy,hRpy,hRqy⟩ := hsaturation y hy
        have hby : b ∈ Uy := by rw [hUeqy]; exact hb
        exact (hSUy b hby).2.2
    have hcut' := hcut Bp hBpSub Q hQsub hBpNonempty hQnonempty hcross
    have hQcard : Q.card=W.card+2 := by simp [Q,hWnotp,hWnotq,hpq,hpq.symm]
    rw [hBpCard,hQcard] at hcut'
    omega
