import AFTD.Prelude
import AFTD.Kb.Tcs.MultigraphTruncation
import AFTD.Kb.Tcs.SimpleGraphIsStrongEdgeColoring
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.Tcs.MultigraphCubicThirdEdge
import AFTD.Kb.Tcs.TruncationLocalStateInternalCover

/-!
# truncation_local_states_strong_coloring_iff

Topic: graphs   Node: 36fc268c4f66

Provenance: formalization of a published result. Source: arXiv:2610.41950 (Strong edge-colourings of truncations of cubic graphs), Lemma 2.1 (the first, signature form; the equivalent form (2.3) and the pole version are not stated)

Lemma 2.1 of arXiv:2610.41950. Let G be a loopless cubic multigraph, given by ends : E → Sym2 V (no Fintype or Finite instance on V or E is assumed: the cubic condition already makes the set of edges at each vertex finite, and the lemma is local) with no edge a loop (¬ (ends e).IsDiag) and every vertex on exactly three edges (Set.ncard {e | v ∈ ends e} = 3), and let Ω be a set of six colours (Fintype.card Ω = 6). Let c h : V → E → Ω be a local state at every vertex v: the six colours c v e and h v e (e ranging over the three edges at v) are pairwise distinct, i.e. ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f, the same for h,  and h v e ≠ c v f for all edges e, f at v (so h v is a bijection from the edges at v onto I_v = Ω \ c v(edges at v)). Then the local states define a strong edge-colouring of the truncation T(G) (truncation_local_states_define_strong_coloring ends c h) if and only if for every edge e and all u v with ends e = s(u, v): c u e = c v e and the exposed pairs P_u(e) = truncation_exposed_pair ends c h u e and P_v(e) = truncation_exposed_pair ends c h v e are disjoint (Disjoint of the two sets).
-/

theorem truncation_local_states_strong_coloring_iff {V E Ω : Type*}
    [Fintype Ω] (hΩ : Fintype.card Ω = 6)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f) :
    truncation_local_states_define_strong_coloring ends c h ↔
      ∀ e u v, ends e = s(u, v) →
        c u e = c v e ∧ Disjoint (truncation_exposed_pair ends c h u e)
          (truncation_exposed_pair ends c h v e) := by
  classical
  have port_ext : ∀ p q : {p : V × E // p.1 ∈ ends p.2}, p.1.1 = q.1.1 → p.1.2 = q.1.2 →
      p = q := fun p q h1 h2 => Subtype.ext (Prod.ext h1 h2)
  have ends_eq : ∀ e u w, u ∈ ends e → w ∈ ends e → u ≠ w → ends e = s(u, w) :=
    fun e u w hu hw hne => (Sym2.mem_and_mem_iff hne).1 ⟨hu, hw⟩
  constructor
  · rintro ⟨χ, hs, hext, hint⟩ e u v huv
    have hu : u ∈ ends e := by rw [huv]; exact Sym2.mem_mk_left u v
    have hv : v ∈ ends e := by rw [huv]; exact Sym2.mem_mk_right u v
    have hne : u ≠ v := by
      intro h'
      apply hloop e
      rw [huv, h']
      exact Sym2.mk_isDiag_iff.2 rfl
    let p : {p : V × E // p.1 ∈ ends p.2} := ⟨(u, e), hu⟩
    let q : {p : V × E // p.1 ∈ ends p.2} := ⟨(v, e), hv⟩
    have hpq : p ≠ q := fun h' => hne (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.1) h')
    refine ⟨?_, ?_⟩
    · have h1 : χ s(p, q) = c u e := hext p q hpq rfl
      have h2 : χ s(q, p) = c v e := hext q p hpq.symm rfl
      rw [Sym2.eq_swap] at h2
      exact h1.symm.trans h2
    · rw [Set.disjoint_left]
      rintro ω ⟨hωu, hωu'⟩ ⟨hωv, hωv'⟩
      obtain ⟨g, hg, hgω⟩ :=
        truncation_local_state_internal_cover hΩ hcubic hc hh hch hωu
      obtain ⟨g', hg', hgω'⟩ :=
        truncation_local_state_internal_cover hΩ hcubic hc hh hch hωv
      have hge : g ≠ e := by rintro rfl; exact hωu' hgω.symm
      have hge' : g' ≠ e := by rintro rfl; exact hωv' hgω'.symm
      obtain ⟨k, hk, hke, hkg, -⟩ := multigraph_cubic_third_edge hcubic hu hg hge.symm
      obtain ⟨k', hk', hke', hkg', -⟩ := multigraph_cubic_third_edge hcubic hv hg' hge'.symm
      let a2 : {p : V × E // p.1 ∈ ends p.2} := ⟨(u, k), hk⟩
      let r : {p : V × E // p.1 ∈ ends p.2} := ⟨(u, g), hg⟩
      let b2 : {p : V × E // p.1 ∈ ends p.2} := ⟨(v, k'), hk'⟩
      let r' : {p : V × E // p.1 ∈ ends p.2} := ⟨(v, g'), hg'⟩
      have hpa2 : p ≠ a2 := fun h' =>
        hke (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h').symm
      have hpr : p ≠ r := fun h' =>
        hge (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h').symm
      have ha2r : a2 ≠ r := fun h' =>
        hkg (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h')
      have hqb2 : q ≠ b2 := fun h' =>
        hke' (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h').symm
      have hqr' : q ≠ r' := fun h' =>
        hge' (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h').symm
      have hb2r' : b2 ≠ r' := fun h' =>
        hkg' (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h')
      have hx : χ s(p, a2) = ω := by
        rw [← hgω]; exact hint p a2 r hpa2 hpr ha2r rfl rfl
      have hy : χ s(q, b2) = ω := by
        rw [← hgω']; exact hint q b2 r' hqb2 hqr' hb2r' rfl rfl
      refine hs s(p, a2) ((SimpleGraph.mem_edgeSet _).2 ⟨hpa2, Or.inl rfl⟩)
        s(q, b2) ((SimpleGraph.mem_edgeSet _).2 ⟨hqb2, Or.inl rfl⟩) ?_
        (Or.inr ⟨p, q, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _, ⟨hpq, Or.inr rfl⟩⟩)
        (hx.trans hy.symm)
      intro h'
      have hmem : p ∈ s(q, b2) := h' ▸ Sym2.mem_mk_left p a2
      rcases Sym2.mem_iff.1 hmem with h'' | h''
      · exact hne (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.1) h'')
      · exact hne (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.1) h'')
  · intro H
    have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
    let Rel : Sym2 {p : V × E // p.1 ∈ ends p.2} → Ω → Prop := fun z ω =>
      (∃ p q : {p : V × E // p.1 ∈ ends p.2}, z = s(p, q) ∧ p ≠ q ∧ p.1.2 = q.1.2 ∧
        ω = c p.1.1 p.1.2) ∨
      (∃ p q r : {p : V × E // p.1 ∈ ends p.2}, z = s(p, q) ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        p.1.1 = q.1.1 ∧ p.1.1 = r.1.1 ∧ ω = h r.1.1 r.1.2)
    let χ : Sym2 {p : V × E // p.1 ∈ ends p.2} → Ω := fun z => Classical.epsilon (Rel z)
    have port_third : ∀ p q r r' : {p : V × E // p.1 ∈ ends p.2}, p ≠ q → p.1.1 = q.1.1 →
        r ≠ p → r ≠ q → r' ≠ p → r' ≠ q → r.1.1 = p.1.1 → r'.1.1 = p.1.1 → r = r' := by
      intro p q r r' hpq hv hrp hrq hr'p hr'q hr hr'
      have hpe : p.1.1 ∈ ends p.1.2 := p.2
      have hqe : p.1.1 ∈ ends q.1.2 := by rw [hv]; exact q.2
      have hef : p.1.2 ≠ q.1.2 := fun h' => hpq (port_ext p q hv h')
      obtain ⟨g, -, -, -, hall⟩ := multigraph_cubic_third_edge hcubic hpe hqe hef
      have hrg : r.1.2 = g := by
        have hre : p.1.1 ∈ ends r.1.2 := by rw [← hr]; exact r.2
        rcases hall _ hre with h' | h' | h'
        · exact absurd (port_ext r p hr h') hrp
        · exact absurd (port_ext r q (hr.trans hv) h') hrq
        · exact h'
      have hr'g : r'.1.2 = g := by
        have hre : p.1.1 ∈ ends r'.1.2 := by rw [← hr']; exact r'.2
        rcases hall _ hre with h' | h' | h'
        · exact absurd (port_ext r' p hr' h') hr'p
        · exact absurd (port_ext r' q (hr'.trans hv) h') hr'q
        · exact h'
      exact port_ext r r' (hr.trans hr'.symm) (hrg.trans hr'g.symm)
    have hext' : ∀ p q : {p : V × E // p.1 ∈ ends p.2}, p ≠ q → p.1.2 = q.1.2 →
        χ s(p, q) = c p.1.1 p.1.2 := by
      intro p q hpq he
      have hR : Rel s(p, q) (c p.1.1 p.1.2) := Or.inl ⟨p, q, rfl, hpq, he, rfl⟩
      have hspec : Rel s(p, q) (χ s(p, q)) := Classical.epsilon_spec ⟨_, hR⟩
      have hvne : p.1.1 ≠ q.1.1 := fun h' => hpq (port_ext p q h' he)
      rcases hspec with ⟨p', q', hz, hpq', he', hω⟩ | ⟨p', q', r', hz, hpq', hpr', hqr', hv1, hv2, hω⟩
      · rw [hω]
        rcases Sym2.eq_iff.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1]
        · rw [← h2, ← he]
          have hq : q.1.1 ∈ ends p.1.2 := by rw [he]; exact q.2
          exact ((H p.1.2 p.1.1 q.1.1 (ends_eq _ _ _ p.2 hq hvne)).1).symm
      · exfalso
        have : p.1.1 = q.1.1 := by
          rcases Sym2.eq_iff.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hv1
          · rw [h1, h2]; exact hv1.symm
        exact hvne this
    have hint' : ∀ p q r : {p : V × E // p.1 ∈ ends p.2}, p ≠ q → p ≠ r → q ≠ r →
        p.1.1 = q.1.1 → p.1.1 = r.1.1 → χ s(p, q) = h r.1.1 r.1.2 := by
      intro p q r hpq hpr hqr hv hvr
      have hR : Rel s(p, q) (h r.1.1 r.1.2) := Or.inr ⟨p, q, r, rfl, hpq, hpr, hqr, hv, hvr, rfl⟩
      have hspec : Rel s(p, q) (χ s(p, q)) := Classical.epsilon_spec ⟨_, hR⟩
      rcases hspec with ⟨p', q', hz, hpq', he', hω⟩ | ⟨p', q', r', hz, hpq', hpr', hqr', hv1, hv2, hω⟩
      · exfalso
        have : p.1.2 = q.1.2 := by
          rcases Sym2.eq_iff.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact he'
          · rw [h1, h2]; exact he'.symm
        exact hpq (port_ext p q hv this)
      · rw [hω]
        have key : r' ≠ p ∧ r' ≠ q ∧ r'.1.1 = p.1.1 := by
          rcases Sym2.eq_iff.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact ⟨hpr'.symm, hqr'.symm, hv2.symm⟩
          · rw [h1, h2]; exact ⟨hqr'.symm, hpr'.symm, hv2.symm.trans hv1⟩
        have := port_third p q r' r hpq hv key.1 key.2.1 hpr.symm hqr.symm key.2.2 hvr.symm
        rw [this]
    refine ⟨χ, ?_, hext', hint'⟩
    -- two internal edges at the same vertex with the same opposite port are equal
    have int_eq : ∀ a b a' b' r : {p : V × E // p.1 ∈ ends p.2}, a ≠ b → a' ≠ b' →
        a.1.1 = b.1.1 → a'.1.1 = b'.1.1 → a'.1.1 = a.1.1 →
        r ≠ a → r ≠ b → r ≠ a' → r ≠ b' → r.1.1 = a.1.1 → s(a, b) = s(a', b') := by
      intro a b a' b' r hab ha'b' hv hv' hw hra hrb hra' hrb' hr
      have ha' : a' = a ∨ a' = b := by
        by_contra hcon
        push Not at hcon
        exact hra' (port_third a b r a' hab hv hra hrb hcon.1 hcon.2 hr hw)
      have hb' : b' = a ∨ b' = b := by
        by_contra hcon
        push Not at hcon
        exact hrb' (port_third a b r b' hab hv hra hrb hcon.1 hcon.2 hr (hv'.symm.trans hw))
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
        first | rfl | exact Sym2.eq_swap | exact absurd rfl ha'b'
    have ext_eq : ∀ a b b' : {p : V × E // p.1 ∈ ends p.2}, a ≠ b → a ≠ b' →
        a.1.2 = b.1.2 → a.1.2 = b'.1.2 → b = b' := by
      intro a b b' hab hab' hx hx'
      have hvne : a.1.1 ≠ b.1.1 := fun h' => hab (port_ext a b h' hx)
      have hvne' : a.1.1 ≠ b'.1.1 := fun h' => hab' (port_ext a b' h' hx')
      have hb : b'.1.1 ∈ ends a.1.2 := by rw [hx']; exact b'.2
      have hb0 : b.1.1 ∈ ends a.1.2 := by rw [hx]; exact b.2
      rw [ends_eq a.1.2 a.1.1 b.1.1 a.2 hb0 hvne, Sym2.mem_iff] at hb
      rcases hb with h' | h'
      · exact absurd h'.symm hvne'
      · exact port_ext b b' h'.symm (hx.symm.trans hx')
    -- the colour of an internal edge at `a`
    have int_col : ∀ a b : {p : V × E // p.1 ∈ ends p.2}, a ≠ b → a.1.1 = b.1.1 →
        ∃ g, a.1.1 ∈ ends g ∧ g ≠ a.1.2 ∧ g ≠ b.1.2 ∧ χ s(a, b) = h a.1.1 g := by
      intro a b hab hv
      have hb : a.1.1 ∈ ends b.1.2 := by rw [hv]; exact b.2
      have hef : a.1.2 ≠ b.1.2 := fun h' => hab (port_ext a b hv h')
      obtain ⟨g, hg, hga, hgb, -⟩ := multigraph_cubic_third_edge hcubic a.2 hb hef
      refine ⟨g, hg, hga, hgb, ?_⟩
      have hra : a ≠ ⟨(a.1.1, g), hg⟩ := fun h' =>
        hga (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h').symm
      have hrb : b ≠ ⟨(a.1.1, g), hg⟩ := fun h' =>
        hgb (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h').symm
      exact hint' a b ⟨(a.1.1, g), hg⟩ hab hra hrb hv rfl
    have around : ∀ a b a' b' : {p : V × E // p.1 ∈ ends p.2},
        (multigraph_truncation ends).Adj a b → (multigraph_truncation ends).Adj a' b' →
        a.1.1 = a'.1.1 → s(a, b) ≠ s(a', b') → χ s(a, b) ≠ χ s(a', b') := by
      intro a b a' b' hab ha'b' hw hne heq
      obtain ⟨hab1, hab2⟩ := hab
      obtain ⟨ha'b'1, ha'b'2⟩ := ha'b'
      rcases hab2 with hi | hx <;> rcases ha'b'2 with hi' | hx'
      · obtain ⟨g, hg, hga, hgb, hcol⟩ := int_col a b hab1 hi
        obtain ⟨g', hg', hga', hgb', hcol'⟩ := int_col a' b' ha'b'1 hi'
        rw [hcol, hcol', ← hw] at heq
        have hg'' : a.1.1 ∈ ends g' := by rw [hw]; exact hg'
        have hgg : g = g' := hh _ _ _ hg hg'' heq
        subst hgg
        refine hne (int_eq a b a' b' ⟨(a.1.1, g), hg⟩ hab1 ha'b'1 hi hi' hw.symm ?_ ?_ ?_ ?_ rfl)
        · exact fun h' => hga (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h')
        · exact fun h' => hgb (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h')
        · exact fun h' => hga' (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h')
        · exact fun h' => hgb' (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.2) h')
      · obtain ⟨g, hg, -, -, hcol⟩ := int_col a b hab1 hi
        rw [hcol, hext' a' b' ha'b'1 hx', ← hw] at heq
        have ha'e : a.1.1 ∈ ends a'.1.2 := by rw [hw]; exact a'.2
        exact hch _ _ _ hg ha'e heq
      · obtain ⟨g', hg', -, -, hcol'⟩ := int_col a' b' ha'b'1 hi'
        rw [hext' a b hab1 hx, hcol', ← hw] at heq
        have hg'' : a.1.1 ∈ ends g' := by rw [hw]; exact hg'
        exact hch _ _ _ hg'' a.2 heq.symm
      · rw [hext' a b hab1 hx, hext' a' b' ha'b'1 hx', ← hw] at heq
        have ha'e : a.1.1 ∈ ends a'.1.2 := by rw [hw]; exact a'.2
        have hee : a.1.2 = a'.1.2 := hc _ _ _ a.2 ha'e heq
        have haa : a = a' := port_ext a a' hw hee
        subst haa
        exact hne (by rw [ext_eq a b b' hab1 ha'b'1 hx hx'])
    have around2 : ∀ x y : Sym2 {p : V × E // p.1 ∈ ends p.2},
        x ∈ (multigraph_truncation ends).edgeSet → y ∈ (multigraph_truncation ends).edgeSet →
        x ≠ y → ∀ z z', z ∈ x → z' ∈ y → z.1.1 = z'.1.1 → χ x ≠ χ y := by
      intro x y hx hy hxy z z' hz hz' hzz
      obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hz
      obtain ⟨b', rfl⟩ := Sym2.mem_iff_exists.1 hz'
      exact around z b z' b' ((SimpleGraph.mem_edgeSet _).1 hx)
        ((SimpleGraph.mem_edgeSet _).1 hy) hzz hxy
    intro x hx y hy hxy hconf
    rcases hconf with ⟨z, hz1, hz2⟩ | ⟨u, w, hu, hw, huw⟩
    · exact around2 x y hx hy hxy z z hz1 hz2 rfl
    · obtain ⟨huw1, huw2⟩ := huw
      rcases huw2 with hv | he
      · exact around2 x y hx hy hxy u w hu hw hv
      · obtain ⟨u2, rfl⟩ := Sym2.mem_iff_exists.1 hu
        obtain ⟨w2, rfl⟩ := Sym2.mem_iff_exists.1 hw
        have hadj := (SimpleGraph.mem_edgeSet _).1 hx
        have hadj' := (SimpleGraph.mem_edgeSet _).1 hy
        have hvne : u.1.1 ≠ w.1.1 := fun h' => huw1 (port_ext u w h' he)
        by_cases hx2 : u.1.1 = u2.1.1
        · by_cases hy2 : w.1.1 = w2.1.1
          · obtain ⟨g, hg, hgu, -, hcol⟩ := int_col u u2 hadj.1 hx2
            obtain ⟨g', hg', hgw, -, hcol'⟩ := int_col w w2 hadj'.1 hy2
            have hwe : w.1.1 ∈ ends u.1.2 := by rw [he]; exact w.2
            have hdisj := (H u.1.2 u.1.1 w.1.1 (ends_eq _ _ _ u.2 hwe hvne)).2
            have m1 : χ s(u, u2) ∈ truncation_exposed_pair ends c h u.1.1 u.1.2 := by
              rw [hcol]
              exact ⟨fun f hf => (hch _ _ _ hg hf).symm, fun h' => hgu (hh _ _ _ hg u.2 h')⟩
            have m2 : χ s(w, w2) ∈ truncation_exposed_pair ends c h w.1.1 u.1.2 := by
              rw [hcol', he]
              exact ⟨fun f hf => (hch _ _ _ hg' hf).symm, fun h' => hgw (hh _ _ _ hg' w.2 h')⟩
            intro heq
            rw [heq] at m1
            exact Set.disjoint_left.1 hdisj m1 m2
          · -- `s(w, w2)` is external, so `w2 = u`
            have hw2 : w.1.2 = w2.1.2 := hadj'.2.resolve_left hy2
            have hwu : w ≠ u := fun h' => huw1 h'.symm
            have : w2 = u := ext_eq w w2 u hadj'.1 hwu hw2 he.symm
            subst this
            exact around2 _ _ hx hy hxy w2 w2 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _) rfl
        · have hu2 : u.1.2 = u2.1.2 := hadj.2.resolve_left hx2
          have : u2 = w := ext_eq u u2 w hadj.1 huw1 hu2 he
          subst this
          exact around2 _ _ hx hy hxy u2 u2 (Sym2.mem_mk_right _ _) (Sym2.mem_mk_left _ _) rfl
