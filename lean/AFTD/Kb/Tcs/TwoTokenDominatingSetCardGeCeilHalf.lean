import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphDominationNumber

/-!
# two_token_dominating_set_card_ge_ceil_half

Topic: graphs   Node: c9d4376e7d28

Provenance: helper lemma. arXiv:2611.15124, Theorem 1.3

Let G be a finite simple graph on vertex type V with domination number at least 2. Then every dominating set D of the 2-token graph F_2(G) satisfies (Fintype.card V + 1) / 2 ≤ D.card.
-/

/-- Every dominating set of the 2-token graph F_2(G) has cardinality at least ceil(n/2) when G has domination number at least 2. -/
theorem two_token_dominating_set_card_ge_ceil_half {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hγ : 2 ≤ simple_graph_domination_number G)
    (D : Finset { s : Finset V // s.card = 2 })
    (hD : simple_graph_is_dominating (token_graph G 2) (D : Set { s : Finset V // s.card = 2 })) :
    (Fintype.card V + 1) / 2 ≤ D.card := by
  classical
  set U : Finset V := D.biUnion (fun s => s.val) with hUdef
  have hsubU : ∀ s ∈ D, s.val ⊆ U := by
    intro s hs v hv
    rw [hUdef]
    exact Finset.mem_biUnion.mpr ⟨s, hs, hv⟩
  have hUle : U.card ≤ 2 * D.card := by
    calc U.card ≤ ∑ s ∈ D, (s.val).card := Finset.card_biUnion_le
      _ = ∑ _s ∈ D, 2 := by
          apply Finset.sum_congr rfl
          intro s _
          exact s.property
      _ = 2 * D.card := by
          simp [Finset.sum_const, mul_comm]
  have hcompl : (Finset.univ \ U).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    by_contra hxy
    have hxU : x ∉ U := (Finset.mem_sdiff.mp hx).2
    have hyU : y ∉ U := (Finset.mem_sdiff.mp hy).2
    have hcard2 : ({x, y} : Finset V).card = 2 := Finset.card_pair hxy
    rcases hD (⟨{x,y}, hcard2⟩ : {s : Finset V // s.card = 2}) with hzD | ⟨u, huD, hadj⟩
    · apply hxU
      rw [hUdef]
      exact Finset.mem_biUnion.mpr ⟨_, hzD, by simp⟩
    · obtain ⟨p, q, hpq, hdiff⟩ := hadj
      have huU : ∀ v ∈ u.val, v ∈ U := hsubU u huD
      have hpos : 0 < u.val.card := by rw [u.property]; norm_num
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have haU : a ∈ U := huU a ha
      have hax : a ≠ x := fun h => hxU (h ▸ haU)
      have hay : a ≠ y := fun h => hyU (h ▸ haU)
      have hdiff' : symmDiff u.val ({x, y} : Finset V) = {p, q} := hdiff
      have hxS : x ∈ symmDiff u.val ({x, y} : Finset V) := by
        rw [Finset.mem_symmDiff]
        exact Or.inr ⟨by simp, fun hxmem => hxU (huU x hxmem)⟩
      have hyS : y ∈ symmDiff u.val ({x, y} : Finset V) := by
        rw [Finset.mem_symmDiff]
        exact Or.inr ⟨by simp, fun hymem => hyU (huU y hymem)⟩
      have haS : a ∈ symmDiff u.val ({x, y} : Finset V) := by
        rw [Finset.mem_symmDiff]
        refine Or.inl ⟨ha, ?_⟩
        intro hav
        rcases Finset.mem_insert.mp hav with h | h
        · exact hax h
        · rw [Finset.mem_singleton] at h
          exact hay h
      have hsub : ({a, x, y} : Finset V) ⊆ ({p, q} : Finset V) := by
        intro v hv
        rw [← hdiff']
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact haS
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hxS
        · rw [Finset.mem_singleton] at hv
          subst hv
          exact hyS
      have h3 : ({a, x, y} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hax, hay]),
            Finset.card_insert_of_notMem (by simp [hxy]),
            Finset.card_singleton]
      have h2 : ({p, q} : Finset V).card = 2 := Finset.card_pair (G.ne_of_adj hpq)
      have := Finset.card_le_card hsub
      omega
  have hsplit : Fintype.card V = U.card + (Finset.univ \ U).card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
    rw [Finset.card_univ] at h
    omega
  suffices hmain : Fintype.card V ≤ 2 * D.card by omega
  by_contra hlt
  have hn : Fintype.card V = 2 * D.card + 1 := by omega
  have hUeq : U.card = 2 * D.card := by omega
  have hcompeq : (Finset.univ \ U).card = 1 := by omega
  have hWpos : 0 < (Finset.univ \ U).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hWpos
  have hwU : w ∉ U := (Finset.mem_sdiff.mp hw).2
  have hWuniq : ∀ x ∈ Finset.univ \ U, x = w := by
    have h := Finset.card_le_one.mp hcompl
    exact fun x hx => h x hx w hw
  have hznondom : ∃ z : V, z ≠ w ∧ ¬ G.Adj w z := by
    by_contra h
    push Not at h
    have hdom : simple_graph_is_dominating G (({w} : Finset V) : Set V) := by
      intro v
      by_cases hv : v = w
      · left; simp [hv]
      · right; exact ⟨w, by simp, h v hv⟩
    have hmem : 1 ∈ {k : ℕ | ∃ S : Finset V, simple_graph_is_dominating G (S : Set V) ∧ S.card = k} :=
      ⟨{w}, hdom, by simp⟩
    have hle : simple_graph_domination_number G ≤ 1 := Nat.sInf_le hmem
    omega
  obtain ⟨z, hzw, hzw'⟩ := hznondom
  have hzU : z ∈ U := by
    by_contra hz
    have : z ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
    exact hzw (hWuniq z this)
  obtain ⟨s, hsD, hzs⟩ := Finset.mem_biUnion.mp hzU
  have hsval : s.val ⊆ U := hsubU s hsD
  have hscard : (s.val.erase z).card = 1 := by
    rw [Finset.card_erase_of_mem hzs, s.property]
  obtain ⟨z', hz'E⟩ := Finset.card_eq_one.mp hscard
  have hz'erase : z' ∈ s.val.erase z := by rw [hz'E]; exact Finset.mem_singleton_self z'
  have hz'ne : z' ≠ z := (Finset.mem_erase.mp hz'erase).1
  have hz'mem : z' ∈ s.val := (Finset.mem_erase.mp hz'erase).2
  have hs_eq : s.val = {z, z'} := by
    conv_lhs => rw [← Finset.insert_erase hzs]
    rw [hz'E]
  have hz'U : z' ∈ U := hsval hz'mem
  have hwz' : w ≠ z' := fun h => hwU (h ▸ hz'U)
  set y : { s : Finset V // s.card = 2 } := ⟨{w, z'}, Finset.card_pair hwz'⟩ with hydef
  have hyval : y.val = ({w, z'} : Finset V) := rfl
  have hynd : y ∉ D := by
    intro hy
    apply hwU
    rw [hUdef]
    exact Finset.mem_biUnion.mpr ⟨y, hy, by rw [hyval]; simp⟩
  have hdomy : ∃ t ∈ D, (token_graph G 2).Adj t y := by
    rcases hD y with hy | ⟨t, htD, hadj⟩
    · exact absurd hy hynd
    · exact ⟨t, htD, hadj⟩
  obtain ⟨t, htD, hadj⟩ := hdomy
  obtain ⟨p, q, hpq, hdiff⟩ := hadj
  have htU : ∀ v ∈ t.val, v ∈ U := hsubU t htD
  have hwt : w ∉ t.val := fun h => hwU (htU w h)
  have hz't : z' ∈ t.val := by
    by_contra hz'nt
    have hdisj : Disjoint t.val y.val := by
      rw [Finset.disjoint_left]
      intro v hv hvy
      rw [hyval] at hvy
      rcases Finset.mem_insert.mp hvy with rfl | hvy
      · exact hwt hv
      · rw [Finset.mem_singleton] at hvy
        exact hz'nt (hvy ▸ hv)
    have hsym : symmDiff t.val y.val = t.val ∪ y.val := Finset.symmDiff_eq_union hdisj
    have hc4 : (t.val ∪ y.val).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj, t.property, hyval, Finset.card_pair hwz']
    have hc2 : (symmDiff t.val y.val).card = 2 := by
      rw [hdiff]; exact Finset.card_pair (G.ne_of_adj hpq)
    rw [hsym] at hc2
    omega
  have hterase : (t.val.erase z').card = 1 := by
    rw [Finset.card_erase_of_mem hz't, t.property]
  obtain ⟨b', hb'E⟩ := Finset.card_eq_one.mp hterase
  have hb'erase : b' ∈ t.val.erase z' := by rw [hb'E]; exact Finset.mem_singleton_self b'
  have hb'ne : b' ≠ z' := (Finset.mem_erase.mp hb'erase).1
  have hb'mem : b' ∈ t.val := (Finset.mem_erase.mp hb'erase).2
  have ht_eq : t.val = {z', b'} := by
    conv_lhs => rw [← Finset.insert_erase hz't]
    rw [hb'E]
  have hwS : w ∈ symmDiff t.val y.val := by
    rw [Finset.mem_symmDiff]
    exact Or.inr ⟨by rw [hyval]; simp, hwt⟩
  have hb'S : b' ∈ symmDiff t.val y.val := by
    rw [Finset.mem_symmDiff]
    refine Or.inl ⟨hb'mem, ?_⟩
    rw [hyval]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hwU (h ▸ htU b' hb'mem), hb'ne⟩
  have hwq : w ∈ ({p, q} : Finset V) := by rw [← hdiff]; exact hwS
  have hb'q : b' ∈ ({p, q} : Finset V) := by rw [← hdiff]; exact hb'S
  have hwb' : w ≠ b' := fun h => hwU (h ▸ htU b' hb'mem)
  have hsubpq : ({w, b'} : Finset V) ⊆ ({p, q} : Finset V) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hwq
    · rw [Finset.mem_singleton] at hv
      subst hv
      exact hb'q
  have heq : ({w, b'} : Finset V) = {p, q} := by
    apply Finset.eq_of_subset_of_card_le hsubpq
    rw [Finset.card_pair (G.ne_of_adj hpq), Finset.card_pair hwb']
  have hwadj : G.Adj w b' := by
    have hp : p ∈ ({w, b'} : Finset V) := by rw [heq]; exact Finset.mem_insert_self p {q}
    have hq : q ∈ ({w, b'} : Finset V) := by rw [heq]; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact absurd (hp.trans hq.symm) (G.ne_of_adj hpq)
    · rw [hp, hq] at hpq; exact hpq
    · rw [hp, hq] at hpq; exact (G.adj_comm b' w).mp hpq
    · exact absurd (hp.trans hq.symm) (G.ne_of_adj hpq)
  by_cases hbz : b' = z
  · exact hzw' (hbz ▸ hwadj)
  · have hst : s ≠ t := by
      intro hst_eq
      have hzt : z ∈ t.val := by rw [← hst_eq]; exact hzs
      rw [ht_eq] at hzt
      rcases Finset.mem_insert.mp hzt with h | h
      · exact hz'ne h.symm
      · rw [Finset.mem_singleton] at h
        exact hbz h.symm
    have hcover : U ⊆ ({z, z', b'} : Finset V) ∪ ((D.erase s).erase t).biUnion (fun u => u.val) := by
      intro v hv
      rw [hUdef] at hv
      obtain ⟨u, huD, hvu⟩ := Finset.mem_biUnion.mp hv
      rw [Finset.mem_union]
      by_cases hus : u = s
      · left
        rw [hus, hs_eq] at hvu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvu ⊢
        tauto
      · by_cases hut : u = t
        · left
          rw [hut, ht_eq] at hvu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hvu ⊢
          tauto
        · right
          exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_erase.mpr ⟨hut, Finset.mem_erase.mpr ⟨hus, huD⟩⟩, hvu⟩
    have hcard_cover : U.card ≤ 3 + 2 * ((D.erase s).erase t).card := by
      have h1 : U.card ≤ (({z, z', b'} : Finset V) ∪ ((D.erase s).erase t).biUnion (fun u => u.val)).card :=
        Finset.card_le_card hcover
      have h2 : (({z, z', b'} : Finset V) ∪ ((D.erase s).erase t).biUnion (fun u => u.val)).card
          ≤ ({z, z', b'} : Finset V).card + (((D.erase s).erase t).biUnion (fun u => u.val)).card :=
        Finset.card_union_le _ _
      have h3 : ({z, z', b'} : Finset V).card ≤ 3 := by
        have ha1 := Finset.card_insert_le z ({z', b'} : Finset V)
        have ha2 := Finset.card_insert_le z' ({b'} : Finset V)
        simp only [Finset.card_singleton] at ha1 ha2
        omega
      have h4 : (((D.erase s).erase t).biUnion (fun u => u.val)).card ≤ 2 * ((D.erase s).erase t).card := by
        calc _ ≤ ∑ u ∈ (D.erase s).erase t, (u.val).card := Finset.card_biUnion_le
          _ = ∑ _u ∈ (D.erase s).erase t, 2 := by
              apply Finset.sum_congr rfl
              intro u _
              exact u.property
          _ = 2 * ((D.erase s).erase t).card := by
              simp [Finset.sum_const, mul_comm]
      omega
    have hD0card : ((D.erase s).erase t).card = D.card - 2 := by
      have ht_erase : t ∈ D.erase s := Finset.mem_erase.mpr ⟨hst.symm, htD⟩
      rw [Finset.card_erase_of_mem ht_erase, Finset.card_erase_of_mem hsD]
      omega
    have hD2 : 2 ≤ D.card := by
      have hsub : ({s, t} : Finset { s : Finset V // s.card = 2 }) ⊆ D := by
        intro u hu
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hsD
        · exact htD
      have h := Finset.card_le_card hsub
      rwa [Finset.card_pair hst] at h
    omega
