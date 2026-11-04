import AFTD.Prelude
import AFTD.Kb.Tcs.WienerIndex

/-!
# wiener_index_add_edges_twin_independent_set

Topic: graphs   Node: 609e024f5c01

Provenance: helper lemma. arXiv:2611.01808 Lemma 2

Let G and H be simple graphs on a finite vertex type V, where G is connected. Suppose Z and X are subsets of V such that 2 ≤ Nat.card X, Z is an independent set in G (∀ u ∈ Z, ∀ v ∈ Z, ¬G.Adj u v), every vertex in Z has open neighborhood X in G (∀ z ∈ Z, G.neighborSet z = X), G ≤ H, and every edge of H is in G or has both endpoints in Z (∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z)). Then the Wiener index of G equals the Wiener index of H plus the number of added edges, wiener_index G = wiener_index H + Nat.card ↑(H.edgeSet \ G.edgeSet).
-/

/-- Adding edges between twin independent vertices reduces the Wiener index by the number of added edges. -/
theorem wiener_index_add_edges_twin_independent_set
    {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (hGconn : G.Connected)
    (Z X : Set V) (hXcard : 2 ≤ Nat.card X)
    (hZindep : ∀ u ∈ Z, ∀ v ∈ Z, ¬G.Adj u v)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X)
    (hGH_le : G ≤ H)
    (hGH_edges : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z)) :
    wiener_index G = wiener_index H + Nat.card ↑(H.edgeSet \ G.edgeSet) := by
  classical
  have hXnon : X.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h; rw [h] at hXcard; simp at hXcard
  have hg_of : ∀ {u v : V}, H.Adj u v → (u ∉ Z ∨ v ∉ Z) → G.Adj u v := by
    intro u v huv h
    rcases hGH_edges u v huv with hg | ⟨hu, hv⟩
    · exact hg
    · rcases h with h' | h'
      · exact absurd hu h'
      · exact absurd hv h'
  have memX_of : ∀ {u v : V}, u ∈ Z → v ∉ Z → H.Adj u v → v ∈ X := by
    intro u v hu hv huv
    have hg : G.Adj u v := hg_of huv (Or.inr hv)
    have hmem : v ∈ G.neighborSet u := hg
    rwa [hZneigh u hu] at hmem
  have adj_of_memX : ∀ {z x : V}, z ∈ Z → x ∈ X → G.Adj z x := by
    intro z x hz hx
    have hmem : x ∈ G.neighborSet z := by rw [hZneigh z hz]; exact hx
    exact hmem
  have compress : ∀ {a b : V} (p : H.Walk a b), ¬ (a ∈ Z ∧ b ∈ Z) → ∃ q : G.Walk a b, q.length ≤ p.length := by
    suffices h : ∀ n, ∀ {a b : V} (p : H.Walk a b), p.length = n → ¬ (a ∈ Z ∧ b ∈ Z) → ∃ q : G.Walk a b, q.length ≤ p.length by
      intro a b p hp
      exact h p.length p rfl hp
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b p hpn hgood
      cases p with
      | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
      | cons hd p' =>
        rename_i c
        have hp' : p'.length + 1 = n := by simpa only [SimpleGraph.Walk.length_cons] using hpn
        have hplen_lt : p'.length < n := by omega
        by_cases haZ : a ∈ Z
        · have hbZ : b ∉ Z := fun hb => hgood ⟨haZ, hb⟩
          by_cases hcZ : c ∈ Z
          · obtain ⟨d, hdmem, hfstZ, hsndZ⟩ := SimpleGraph.Walk.exists_boundary_dart (SimpleGraph.Walk.cons hd p') Z haZ hbZ
            have hsndX : d.toProd.2 ∈ X := memX_of hfstZ hsndZ d.adj
            have hmem : d.toProd.2 ∈ (SimpleGraph.Walk.cons hd p').support :=
              SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hdmem
            have hne : d.toProd.2 ≠ a := by
              intro heq; rw [heq] at hsndZ; exact hsndZ haZ
            set s : H.Walk d.toProd.2 b := (SimpleGraph.Walk.cons hd p').dropUntil d.toProd.2 hmem with hsdef
            have hs_lt : s.length < (SimpleGraph.Walk.cons hd p').length :=
              SimpleGraph.Walk.length_dropUntil_lt_length hmem hne
            have hlt : s.length < n := by
              rw [SimpleGraph.Walk.length_cons] at hs_lt; omega
            obtain ⟨q, hq⟩ := ih s.length hlt s rfl (fun h => hsndZ h.1)
            have hadj : G.Adj a d.toProd.2 := adj_of_memX haZ hsndX
            refine ⟨SimpleGraph.Walk.cons hadj q, ?_⟩
            simp only [SimpleGraph.Walk.length_cons]; omega
          · have hgood' : ¬ (c ∈ Z ∧ b ∈ Z) := fun h => hcZ h.1
            obtain ⟨q, hq⟩ := ih p'.length hplen_lt p' rfl hgood'
            have hgac : G.Adj a c := hg_of hd (Or.inr hcZ)
            refine ⟨SimpleGraph.Walk.cons hgac q, ?_⟩
            simp only [SimpleGraph.Walk.length_cons]; omega
        · by_cases hcZ : c ∈ Z
          · have hgac : G.Adj a c := hg_of hd (Or.inl haZ)
            have haX : a ∈ X := by
              have hmem : a ∈ G.neighborSet c := hgac.symm
              rwa [hZneigh c hcZ] at hmem
            by_cases hbZ : b ∈ Z
            · have hadj : G.Adj a b := (adj_of_memX hbZ haX).symm
              refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
              simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]; omega
            · have hgood' : ¬ (c ∈ Z ∧ b ∈ Z) := fun h => hbZ h.2
              obtain ⟨q, hq⟩ := ih p'.length hplen_lt p' rfl hgood'
              refine ⟨SimpleGraph.Walk.cons hgac q, ?_⟩
              simp only [SimpleGraph.Walk.length_cons]; omega
          · have hgood' : ¬ (c ∈ Z ∧ b ∈ Z) := fun h => hcZ h.1
            obtain ⟨q, hq⟩ := ih p'.length hplen_lt p' rfl hgood'
            have hgac : G.Adj a c := hg_of hd (Or.inl haZ)
            refine ⟨SimpleGraph.Walk.cons hgac q, ?_⟩
            simp only [SimpleGraph.Walk.length_cons]; omega
  have hHconn : H.Connected := hGconn.mono hGH_le
  have hdist_eq : ∀ {u v : V}, ¬ (u ∈ Z ∧ v ∈ Z) → G.dist u v = H.dist u v := by
    intro u v hgood
    refine le_antisymm ?_ ?_
    · obtain ⟨p, hp⟩ := hHconn.exists_walk_length_eq_dist u v
      obtain ⟨q, hq⟩ := compress p hgood
      calc G.dist u v ≤ q.length := SimpleGraph.dist_le q
        _ ≤ p.length := hq
        _ = H.dist u v := hp
    · exact SimpleGraph.Reachable.dist_anti hGH_le (hGconn u v)
  have G_dist_two : ∀ {u v : V}, u ∈ Z → v ∈ Z → u ≠ v → G.dist u v = 2 := by
    intro u v hu hv hne
    have hnadj : ¬ G.Adj u v := hZindep u hu v hv
    have hgt : 1 < G.dist u v := hGconn.one_lt_dist_of_ne_of_not_adj hne hnadj
    have hle : G.dist u v ≤ 2 := by
      obtain ⟨x, hx⟩ := hXnon
      have h1 : G.Adj u x := adj_of_memX hu hx
      have h2 : G.Adj v x := adj_of_memX hv hx
      have hw : G.dist u v ≤ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil)).length :=
        SimpleGraph.dist_le _
      simpa using hw
    omega
  have hpoint : ∀ e : Sym2 V,
      Sym2.lift ⟨fun a b => G.dist a b, fun _ _ => G.dist_comm⟩ e =
      Sym2.lift ⟨fun a b => H.dist a b, fun _ _ => H.dist_comm⟩ e + (if e ∈ H.edgeSet \ G.edgeSet then 1 else 0) := by
      intro e
      induction e using Sym2.ind with
      | _ u v =>
        show G.dist u v = H.dist u v + (if Sym2.mk u v ∈ H.edgeSet \ G.edgeSet then 1 else 0)
        by_cases hnew : Sym2.mk u v ∈ H.edgeSet \ G.edgeSet
        · have hHad : H.Adj u v := (SimpleGraph.mem_edgeSet H).mp hnew.1
          have hnGad : ¬ G.Adj u v := fun hg => hnew.2 ((SimpleGraph.mem_edgeSet G).mpr hg)
          obtain ⟨hu, hv⟩ := (hGH_edges u v hHad).resolve_left hnGad
          have hne : u ≠ v := hHad.ne
          rw [if_pos hnew, G_dist_two hu hv hne, SimpleGraph.dist_eq_one_iff_adj.mpr hHad]
        · rw [if_neg hnew]
          by_cases hbothZ : u ∈ Z ∧ v ∈ Z
          · have hHad : ¬ H.Adj u v := by
              intro hHad
              have hnG : ¬ G.Adj u v := hZindep u hbothZ.1 v hbothZ.2
              exact hnew ⟨(SimpleGraph.mem_edgeSet H).mpr hHad, fun h => hnG ((SimpleGraph.mem_edgeSet G).mp h)⟩
            by_cases hne : u = v
            · subst hne; simp
            · rw [G_dist_two hbothZ.1 hbothZ.2 hne]
              have hle : H.dist u v ≤ 2 := by
                have h := SimpleGraph.Reachable.dist_anti hGH_le (hGconn u v)
                rw [G_dist_two hbothZ.1 hbothZ.2 hne] at h
                exact h
              have hgt : 1 < H.dist u v := hHconn.one_lt_dist_of_ne_of_not_adj hne hHad
              omega
          · exact hdist_eq hbothZ
  have hcard : Nat.card ↑(H.edgeSet \ G.edgeSet) = ∑ e : Sym2 V, (if e ∈ H.edgeSet \ G.edgeSet then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [wiener_index]
  have hsum : (∑ e : Sym2 V, Sym2.lift ⟨fun a b => G.dist a b, fun _ _ => G.dist_comm⟩ e)
      = ∑ e : Sym2 V, (Sym2.lift ⟨fun a b => H.dist a b, fun _ _ => H.dist_comm⟩ e + (if e ∈ H.edgeSet \ G.edgeSet then 1 else 0)) :=
    Finset.sum_congr rfl (fun e _ => hpoint e)
  rw [hsum, Finset.sum_add_distrib, hcard]
