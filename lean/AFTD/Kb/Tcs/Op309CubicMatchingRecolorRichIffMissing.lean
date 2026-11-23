import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_cubic_matching_recolor_rich_iff_missing

Topic: graphs   Node: c0d6525df953

Provenance: helper lemma. Local characterization for the matching-recoloring route to OP-309, checked on 480 cube crossing cases in experiment 31478.

After recoloring a matching in a proper four-edge-coloring with a fifth color, a cubic edge from an unmatched vertex to a matched vertex is rich exactly when the matched vertex’s other nonmatching edge has the color missing at the unmatched vertex.
-/

lemma op309_cubic_matching_recolor_rich_iff_missing_nodup_four {V : Type*} {u v a b : V} (h : [u, v, a, b].Nodup) :
    u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b ∧ a ≠ b := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil] at h
  tauto

lemma op309_cubic_matching_recolor_rich_iff_missing_edges_incident_to_u {V : Type*} (G : SimpleGraph V) (u v a b : V)
    (hNu : ∀ t, G.Adj u t ↔ t = v ∨ t = a ∨ t = b)
    (g : G.edgeSet) (hu : u ∈ g.1) :
    g.1 = s(u, v) ∨ g.1 = s(u, a) ∨ g.1 = s(u, b) := by
  obtain ⟨e, he⟩ := g
  induction e using Sym2.ind with | _ p q =>
  have hadj : G.Adj p q := G.mem_edgeSet.mp he
  have hu_mem : u = p ∨ u = q := Sym2.mem_iff.mp hu
  rcases hu_mem with rfl | rfl
  · have hq : q = v ∨ q = a ∨ q = b := (hNu q).mp hadj
    rcases hq with rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  · have hp : p = v ∨ p = a ∨ p = b := (hNu p).mp hadj.symm
    rcases hp with rfl | rfl | rfl
    · left; exact Sym2.eq_swap
    · right; left; exact Sym2.eq_swap
    · right; right; exact Sym2.eq_swap

lemma op309_cubic_matching_recolor_rich_iff_missing_edges_incident_to_v {V : Type*} (G : SimpleGraph V) (u v x y : V)
    (hNv : ∀ t, G.Adj v t ↔ t = u ∨ t = x ∨ t = y)
    (g : G.edgeSet) (hv : v ∈ g.1) :
    g.1 = s(u, v) ∨ g.1 = s(v, x) ∨ g.1 = s(v, y) := by
  obtain ⟨e, he⟩ := g
  induction e using Sym2.ind with | _ p q =>
  have hadj : G.Adj p q := G.mem_edgeSet.mp he
  have hv_mem : v = p ∨ v = q := Sym2.mem_iff.mp hv
  rcases hv_mem with rfl | rfl
  · have hq : q = u ∨ q = x ∨ q = y := (hNv q).mp hadj
    rcases hq with rfl | rfl | rfl
    · left; exact Sym2.eq_swap
    · right; left; rfl
    · right; right; rfl
  · have hp : p = u ∨ p = x ∨ p = y := (hNv p).mp hadj.symm
    rcases hp with rfl | rfl | rfl
    · left; rfl
    · right; left; exact Sym2.eq_swap
    · right; right; exact Sym2.eq_swap

lemma op309_cubic_matching_recolor_rich_iff_missing_adj_e_cases {V : Type*}
    (G : SimpleGraph V) (u v a b x y : V)
    (hNu : ∀ t, G.Adj u t ↔ t = v ∨ t = a ∨ t = b)
    (hNv : ∀ t, G.Adj v t ↔ t = u ∨ t = x ∨ t = y)
    (e g : G.edgeSet) (he : e.1 = s(u, v))
    (hadj : G.lineGraph.Adj e g) :
    g.1 = s(u, a) ∨ g.1 = s(u, b) ∨ g.1 = s(v, x) ∨ g.1 = s(v, y) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨hne, w, hw1, hw2⟩
  rw [he, Sym2.mem_iff] at hw1
  rcases hw1 with rfl | rfl
  · have hgu := op309_cubic_matching_recolor_rich_iff_missing_edges_incident_to_u G w v a b hNu g hw2
    rcases hgu with h | h | h
    · exfalso; apply hne; exact Subtype.ext (he.trans h.symm)
    · left; exact h
    · right; left; exact h
  · have hgv := op309_cubic_matching_recolor_rich_iff_missing_edges_incident_to_v G u w x y hNv g hw2
    rcases hgv with h | h | h
    · exfalso; apply hne; exact Subtype.ext (he.trans h.symm)
    · right; right; left; exact h
    · right; right; right; exact h

lemma op309_cubic_matching_recolor_rich_iff_missing_fin4_cases (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : Fin 4) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  revert a b c d x
  decide

lemma op309_cubic_matching_recolor_rich_iff_missing_fin4_eq_iff_ne (a b c d x : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxa : x ≠ a) :
    (x ≠ b ∧ x ≠ c) ↔ x = d := by
  constructor
  · intro ⟨hxb, hxc⟩
    rcases op309_cubic_matching_recolor_rich_iff_missing_fin4_cases a b c d hab hac had hbc hbd hcd x with rfl | rfl | rfl | rfl
    · contradiction
    · contradiction
    · contradiction
    · rfl
  · rintro rfl
    exact ⟨hbd.symm, hcd.symm⟩

lemma op309_cubic_matching_recolor_rich_iff_missing_recolor_eq_four (q : Fin 4) (h : (q.val : ℕ) < 5) :
    (⟨q.val, h⟩ : Fin 5) ≠ 4 := by
  intro heq
  have hval : (⟨q.val, h⟩ : Fin 5).val = (4 : Fin 5).val := congrArg Fin.val heq
  change q.val = 4 at hval
  have hq := q.isLt
  omega

lemma op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (M : Finset G.edgeSet)
    (q : G.lineGraph.Coloring (Fin 4)) (c : G.lineGraph.Coloring (Fin 5))
    (hrecolor : ∀ f : G.edgeSet, c f =
      if f ∈ M then 4 else ⟨(q f).val, Nat.lt_trans (q f).isLt (by decide)⟩)
    (g h : G.edgeSet) (hg : g ∈ M) (hh : h ∉ M) :
    c g ≠ c h := by
  rw [hrecolor g, if_pos hg]
  rw [hrecolor h, if_neg hh]
  intro heq
  exact op309_cubic_matching_recolor_rich_iff_missing_recolor_eq_four (q h) _ heq.symm

lemma op309_cubic_matching_recolor_rich_iff_missing_recolor_eq_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (M : Finset G.edgeSet)
    (q : G.lineGraph.Coloring (Fin 4)) (c : G.lineGraph.Coloring (Fin 5))
    (hrecolor : ∀ f : G.edgeSet, c f =
      if f ∈ M then 4 else ⟨(q f).val, Nat.lt_trans (q f).isLt (by decide)⟩)
    (g h : G.edgeSet) (hg : g ∉ M) (hh : h ∉ M) :
    c g = c h ↔ q g = q h := by
  rw [hrecolor g, if_neg hg]
  rw [hrecolor h, if_neg hh]
  constructor
  · intro heq
    have := congrArg Fin.val heq
    exact Fin.ext this
  · intro heq
    rw [heq]

lemma op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (M : Finset G.edgeSet)
    (q : G.lineGraph.Coloring (Fin 4)) (c : G.lineGraph.Coloring (Fin 5))
    (hrecolor : ∀ f : G.edgeSet, c f =
      if f ∈ M then 4 else ⟨(q f).val, Nat.lt_trans (q f).isLt (by decide)⟩)
    (g h : G.edgeSet) (hg : g ∉ M) (hh : h ∉ M) :
    c g ≠ c h ↔ q g ≠ q h :=
  not_congr (op309_cubic_matching_recolor_rich_iff_missing_recolor_eq_iff M q c hrecolor g h hg hh)

theorem op309_cubic_matching_recolor_rich_iff_missing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v a b x y : V) (hu : [u,v,a,b].Nodup) (hv : [v,u,x,y].Nodup)
    (hNu : ∀ t, G.Adj u t ↔ t = v ∨ t = a ∨ t = b)
    (hNv : ∀ t, G.Adj v t ↔ t = u ∨ t = x ∨ t = y)
    (M : Finset G.edgeSet)
    (hmatch : ∀ f ∈ M, ∀ g ∈ M, f ≠ g → ¬ G.lineGraph.Adj f g)
    (hunmatched : ∀ f ∈ M, u ∉ f.1)
    (hmatched : ∃ f ∈ M, f.1 = s(v,x))
    (q : G.lineGraph.Coloring (Fin 4)) (c : G.lineGraph.Coloring (Fin 5))
    (hrecolor : ∀ f : G.edgeSet, c f =
      if f ∈ M then 4 else ⟨(q f).val, Nat.lt_trans (q f).isLt (by decide)⟩)
    (k : Fin 4) (hmissing : ∀ f : G.edgeSet, u ∈ f.1 → q f ≠ k) :
    ∀ e f : G.edgeSet, e.1 = s(u,v) → f.1 = s(v,y) →
      (simple_graph_edge_is_rich G c e ↔ q f = k) := by
  intro e f he hfy
  have hua_adj : G.Adj u a := (hNu a).mpr (Or.inr (Or.inl rfl))
  have hub_adj : G.Adj u b := (hNu b).mpr (Or.inr (Or.inr rfl))
  have hvx_adj : G.Adj v x := (hNv x).mpr (Or.inr (Or.inl rfl))
  let e_ua : G.edgeSet := ⟨s(u, a), G.mem_edgeSet.mpr hua_adj⟩
  let e_ub : G.edgeSet := ⟨s(u, b), G.mem_edgeSet.mpr hub_adj⟩
  let e_vx : G.edgeSet := ⟨s(v, x), G.mem_edgeSet.mpr hvx_adj⟩
  have hua : e_ua.1 = s(u, a) := rfl
  have hub : e_ub.1 = s(u, b) := rfl
  have hvx : e_vx.1 = s(v, x) := rfl
  have ⟨huv, hua_ne, hub_ne, hva, hvb, hab⟩ := op309_cubic_matching_recolor_rich_iff_missing_nodup_four hu
  have ⟨hvu, hvx_ne, hvy_ne, hux, huy, hxy⟩ := op309_cubic_matching_recolor_rich_iff_missing_nodup_four hv
  have hne_e_ua : e ≠ e_ua := by
    intro h; have := congrArg Subtype.val h; rw [he, hua, Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_e_ub : e ≠ e_ub := by
    intro h; have := congrArg Subtype.val h; rw [he, hub, Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_e_vx : e ≠ e_vx := by
    intro h; have := congrArg Subtype.val h; rw [he, hvx, Sym2.eq_iff] at this
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_e_f : e ≠ f := by
    intro h; have := congrArg Subtype.val h; rw [he, hfy, Sym2.eq_iff] at this
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_ua_ub : e_ua ≠ e_ub := by
    intro h; have := congrArg Subtype.val h; rw [hua, hub, Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_ua_vx : e_ua ≠ e_vx := by
    intro h; have := congrArg Subtype.val h; rw [hua, hvx, Sym2.eq_iff] at this
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_ub_vx : e_ub ≠ e_vx := by
    intro h; have := congrArg Subtype.val h; rw [hub, hvx, Sym2.eq_iff] at this
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_ua_f : e_ua ≠ f := by
    intro h; have := congrArg Subtype.val h; rw [hua, hfy, Sym2.eq_iff] at this
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_ub_f : e_ub ≠ f := by
    intro h; have := congrArg Subtype.val h; rw [hub, hfy, Sym2.eq_iff] at this
    rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> contradiction
  have hne_vx_f : e_vx ≠ f := by
    intro h; have := congrArg Subtype.val h; rw [hvx, hfy, Sym2.eq_iff] at this
    rcases this with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> contradiction
  have hadj_ua : G.lineGraph.Adj e e_ua := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨hne_e_ua, u, ?_, ?_⟩
    · rw [he]; exact Sym2.mem_mk_left u v
    · rw [hua]; exact Sym2.mem_mk_left u a
  have hadj_ub : G.lineGraph.Adj e e_ub := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨hne_e_ub, u, ?_, ?_⟩
    · rw [he]; exact Sym2.mem_mk_left u v
    · rw [hub]; exact Sym2.mem_mk_left u b
  have hadj_vx : G.lineGraph.Adj e e_vx := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨hne_e_vx, v, ?_, ?_⟩
    · rw [he]; exact Sym2.mem_mk_right u v
    · rw [hvx]; exact Sym2.mem_mk_left v x
  have hadj_f : G.lineGraph.Adj e f := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨hne_e_f, v, ?_, ?_⟩
    · rw [he]; exact Sym2.mem_mk_right u v
    · rw [hfy]; exact Sym2.mem_mk_left v y
  have hadj_ua_ub : G.lineGraph.Adj e_ua e_ub := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨hne_ua_ub, u, ?_, ?_⟩
    · rw [hua]; exact Sym2.mem_mk_left u a
    · rw [hub]; exact Sym2.mem_mk_left u b
  have h_e_vx_in_M : e_vx ∈ M := by
    obtain ⟨g, hgM, hg1⟩ := hmatched
    have : g = e_vx := Subtype.ext (hg1.trans hvx.symm)
    rwa [this] at hgM
  have h_e_ua_not_M : e_ua ∉ M := by
    intro h
    have := hunmatched e_ua h
    rw [hua] at this
    exact this (Sym2.mem_mk_left u a)
  have h_e_ub_not_M : e_ub ∉ M := by
    intro h
    have := hunmatched e_ub h
    rw [hub] at this
    exact this (Sym2.mem_mk_left u b)
  have h_f_not_M : f ∉ M := by
    intro hfM
    have hadj : G.lineGraph.Adj f e_vx := by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨hne_vx_f.symm, v, ?_, ?_⟩
      · rw [hfy]; exact Sym2.mem_mk_left v y
      · rw [hvx]; exact Sym2.mem_mk_left v x
    exact hmatch f hfM e_vx h_e_vx_in_M hne_vx_f.symm hadj
  have hadj_cases : ∀ g : G.edgeSet, G.lineGraph.Adj e g →
      g = e_ua ∨ g = e_ub ∨ g = e_vx ∨ g = f := by
    intro g hadj
    have hc := op309_cubic_matching_recolor_rich_iff_missing_adj_e_cases G u v a b x y hNu hNv e g he hadj
    rcases hc with h | h | h | h
    · left; exact Subtype.ext (h.trans hua.symm)
    · right; left; exact Subtype.ext (h.trans hub.symm)
    · right; right; left; exact Subtype.ext (h.trans hvx.symm)
    · right; right; right; exact Subtype.ext (h.trans hfy.symm)
  have hq_e_ua_ne_ub : q e_ua ≠ q e_ub := q.valid hadj_ua_ub
  have hq_e_ne_ua : q e ≠ q e_ua := q.valid hadj_ua
  have hq_e_ne_ub : q e ≠ q e_ub := q.valid hadj_ub
  have hq_e_ne_k : q e ≠ k := by
    apply hmissing e
    rw [he]; exact Sym2.mem_mk_left u v
  have hq_e_ua_ne_k : q e_ua ≠ k := by
    apply hmissing e_ua
    rw [hua]; exact Sym2.mem_mk_left u a
  have hq_e_ub_ne_k : q e_ub ≠ k := by
    apply hmissing e_ub
    rw [hub]; exact Sym2.mem_mk_left u b
  have hq_f_ne_e : q f ≠ q e := (q.valid hadj_f).symm
  have h_fin4_iff := op309_cubic_matching_recolor_rich_iff_missing_fin4_eq_iff_ne
    (q e) (q e_ua) (q e_ub) k (q f)
    hq_e_ne_ua hq_e_ne_ub hq_e_ne_k hq_e_ua_ne_ub hq_e_ua_ne_k hq_e_ub_ne_k hq_f_ne_e
  constructor
  · intro hrich
    have h1 : c f ≠ c e_ua := hrich f e_ua hadj_f hadj_ua hne_ua_f.symm
    have h2 : c f ≠ c e_ub := hrich f e_ub hadj_f hadj_ub hne_ub_f.symm
    rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor f e_ua h_f_not_M h_e_ua_not_M] at h1
    rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor f e_ub h_f_not_M h_e_ub_not_M] at h2
    exact h_fin4_iff.mp ⟨h1, h2⟩
  · intro hqfk
    have h12 : q f ≠ q e_ua ∧ q f ≠ q e_ub := h_fin4_iff.mpr hqfk
    intro g₁ g₂ hg₁ hg₂ hne
    have hg1_c := hadj_cases g₁ hg₁
    have hg2_c := hadj_cases g₂ hg₂
    rcases hg1_c with rfl | rfl | rfl | h1f <;>
    rcases hg2_c with rfl | rfl | rfl | h2f
    · contradiction
    · rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor e_ua e_ub h_e_ua_not_M h_e_ub_not_M]
      exact hq_e_ua_ne_ub
    · exact (op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem M q c hrecolor e_vx e_ua h_e_vx_in_M h_e_ua_not_M).symm
    · rw [h2f]
      rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor e_ua f h_e_ua_not_M h_f_not_M]
      exact h12.1.symm
    · rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor e_ub e_ua h_e_ub_not_M h_e_ua_not_M]
      exact hq_e_ua_ne_ub.symm
    · contradiction
    · exact (op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem M q c hrecolor e_vx e_ub h_e_vx_in_M h_e_ub_not_M).symm
    · rw [h2f]
      rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor e_ub f h_e_ub_not_M h_f_not_M]
      exact h12.2.symm
    · exact op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem M q c hrecolor e_vx e_ua h_e_vx_in_M h_e_ua_not_M
    · exact op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem M q c hrecolor e_vx e_ub h_e_vx_in_M h_e_ub_not_M
    · contradiction
    · rw [h2f]
      exact op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem M q c hrecolor e_vx f h_e_vx_in_M h_f_not_M
    · rw [h1f]
      rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor f e_ua h_f_not_M h_e_ua_not_M]
      exact h12.1
    · rw [h1f]
      rw [op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_iff M q c hrecolor f e_ub h_f_not_M h_e_ub_not_M]
      exact h12.2
    · rw [h1f]
      exact (op309_cubic_matching_recolor_rich_iff_missing_recolor_ne_of_mem_not_mem M q c hrecolor e_vx f h_e_vx_in_M h_f_not_M).symm
    · rw [h1f, h2f] at hne
      contradiction
