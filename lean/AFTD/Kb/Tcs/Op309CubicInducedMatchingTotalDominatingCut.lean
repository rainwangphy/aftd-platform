import AFTD.Prelude
import AFTD.Kb.Tcs.MaxDegreeLeTwoExistsRichNeighborFiveColoring
import AFTD.Kb.Tcs.F

/-!
# op309_cubic_induced_matching_total_dominating_cut

Topic: graphs   Node: af71e3667dac

Provenance: helper lemma. A maximal induced matching gives the desired cut, a structural step in the matching recoloring route for OP-309.

Every finite connected simple cubic graph has an induced matching whose covered-vertex cut totally edge-dominates the graph.
-/

namespace op309_cubic_induced_matching_total_dominating_cut

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `S` is an induced matching in the line graph: pairwise non-adjacent and with no common line-graph neighbour. -/
def Ind (S : Finset G.edgeSet) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
    ¬ G.lineGraph.Adj e f ∧ ¬ ∃ g, G.lineGraph.Adj e g ∧ G.lineGraph.Adj f g

/-- `v` is covered by the edge set `S`. -/
def Cov (S : Finset G.edgeSet) (v : V) : Prop :=
  ∃ g ∈ S, v ∈ (g : Sym2 V)

lemma sym2_exists_eq {p : Sym2 V} {a : V} (ha : a ∈ p) : ∃ b, p = s(a, b) := by
  revert ha
  refine Sym2.ind (fun x y ha => ?_) p
  rw [Sym2.mem_iff] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, rfl⟩
  · exact ⟨x, Sym2.eq_swap⟩

lemma sym2_exists_pair (p : Sym2 V) : ∃ a b, p = s(a, b) := by
  refine Sym2.ind (fun x y => ?_) p
  exact ⟨x, y, rfl⟩

lemma sym2_eq_of_mem {p : Sym2 V} {a b : V} (ha : a ∈ p) (hb : b ∈ p) (hab : a ≠ b) :
    p = s(a, b) :=
  (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩

/-- The edge with endpoints `x, y`, given `G.Adj x y`. -/
def edgeOfAdj {x y : V} (h : G.Adj x y) : G.edgeSet := ⟨s(x, y), (SimpleGraph.mem_edgeSet G).mpr h⟩

@[simp] lemma edgeOfAdj_val {x y : V} (h : G.Adj x y) :
    ((edgeOfAdj h : G.edgeSet) : Sym2 V) = s(x, y) := rfl

/-- If `a` lies on the `S`-edge `m` and `e ≠ m` is a different edge through `a` with other endpoint `c`,
then `c` is not covered. -/
lemma not_cov_other {S : Finset G.edgeSet} (hS : Ind S) {m e : G.edgeSet} (hm : m ∈ S)
    {a c : V} (ha : a ∈ (m : Sym2 V)) (he : (e : Sym2 V) = s(a, c)) (hne : e ≠ m) :
    ¬ Cov S c := by
  intro hc
  obtain ⟨h, hh, hch⟩ := hc
  obtain ⟨a_m, hm_eq⟩ := sym2_exists_eq ha
  have hae : a ∈ (e : Sym2 V) := by rw [he]; exact Sym2.mem_mk_left a c
  have hce : c ∈ (e : Sym2 V) := by rw [he]; exact Sym2.mem_mk_right a c
  have hac : a ≠ c := by
    intro hEq; subst hEq
    exact SimpleGraph.irrefl G (he ▸ e.2)
  have hca_m : c ≠ a_m := by
    intro hEq
    apply hne
    apply Subtype.ext
    rw [he, hm_eq, hEq]
  have hc_m : c ∉ (m : Sym2 V) := by
    rw [hm_eq, Sym2.mem_iff]
    simp only [not_or]
    exact ⟨fun h => hac h.symm, hca_m⟩
  have hh_ne_m : h ≠ m := fun hEq => hc_m (hEq ▸ hch)
  have hmh : m ≠ h := hh_ne_m.symm
  by_cases hhe : h = e
  · apply (hS m hm h hh hmh).1
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨hmh, a, ha, ?_⟩
    rw [hhe]; exact hae
  · apply (hS m hm h hh hmh).2
    refine ⟨e, ?_, ?_⟩
    · rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨hne.symm, a, ha, hae⟩
    · rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨hhe, c, hch, hce⟩

/-- At a covered vertex `a` of degree 3, any incident edge `e` has a *different* cut edge `f` through `a`
(other endpoint uncovered), whose line-graph adjacency with `e` gives a total domination witness. -/
lemma exists_cut_at {S : Finset G.edgeSet} (hS : Ind S) {a : V} (hdeg : G.degree a = 3)
    (ha : Cov S a) {e : G.edgeSet} (hae : a ∈ (e : Sym2 V)) :
    ∃ f : G.edgeSet, f ≠ e ∧ a ∈ (f : Sym2 V) ∧ ∃ c : V, (f : Sym2 V) = s(a, c) ∧ ¬ Cov S c := by
  obtain ⟨m, hm, ham⟩ := ha
  obtain ⟨a_m, hm_eq⟩ := sym2_exists_eq ham
  have ham_adj : G.Adj a a_m := (SimpleGraph.mem_edgeSet G).mp (hm_eq ▸ m.2)
  have ha_ne_am : a ≠ a_m := G.ne_of_adj ham_adj
  have ha_m_mem : a_m ∈ G.neighborFinset a := (SimpleGraph.mem_neighborFinset G a a_m).mpr ham_adj
  have hcard : (G.neighborFinset a).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨b, hb_eq⟩ := sym2_exists_eq hae
  have hab_adj : G.Adj a b := (SimpleGraph.mem_edgeSet G).mp (hb_eq ▸ e.2)
  have hb_mem : b ∈ G.neighborFinset a := (SimpleGraph.mem_neighborFinset G a b).mpr hab_adj
  have hab : a ≠ b := G.ne_of_adj hab_adj
  have hTsub : ({b} ∪ {a_m} : Finset V) ⊆ G.neighborFinset a := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hTcard : ({b} ∪ {a_m} : Finset V).card ≤ 2 := by
    calc _ ≤ ({b} : Finset V).card + ({a_m} : Finset V).card := Finset.card_union_le _ _
      _ = 2 := by simp
  have hnonempty : (G.neighborFinset a \ ({b} ∪ {a_m})).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hTsub]
    omega
  obtain ⟨c, hc⟩ := hnonempty
  rw [Finset.mem_sdiff] at hc
  obtain ⟨hcN, hcT⟩ := hc
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hcT
  obtain ⟨hcb, hca_m⟩ := hcT
  have hac_adj : G.Adj a c := (SimpleGraph.mem_neighborFinset G a c).mp hcN
  refine ⟨edgeOfAdj hac_adj, ?_, ?_, c, rfl, ?_⟩
  · intro hfe
    have hv : s(a, c) = s(a, b) := by
      have h1 := congrArg (fun x : G.edgeSet => (x : Sym2 V)) hfe
      simpa only [edgeOfAdj_val, hb_eq] using h1
    rcases Sym2.eq_iff.mp hv with ⟨_, h⟩ | ⟨h, _⟩
    · exact hcb h
    · exact absurd h hab
  · simp only [edgeOfAdj_val]
    exact Sym2.mem_mk_left a c
  · apply not_cov_other hS hm ham (he := edgeOfAdj_val hac_adj) (hne := ?_)
    intro hfm
    have hv : s(a, c) = s(a, a_m) := by
      have h1 := congrArg (fun x : G.edgeSet => (x : Sym2 V)) hfm
      simpa only [edgeOfAdj_val, hm_eq] using h1
    rcases Sym2.eq_iff.mp hv with ⟨_, h⟩ | ⟨h, _⟩
    · exact hca_m h
    · exact absurd h ha_ne_am

/-- A maximum-cardinality induced matching exists. -/
lemma exists_max_induced :
    ∃ S : Finset G.edgeSet, Ind S ∧ ∀ T : Finset G.edgeSet, Ind T → T.card ≤ S.card := by
  classical
  set F : Finset (Finset G.edgeSet) := Finset.univ.filter (fun S => Ind S) with hFdef
  have hne : F.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hFdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp [Ind]⟩
  obtain ⟨S, hSF, hmax⟩ := Finset.exists_max_image F (fun S => S.card) hne
  rw [hFdef, Finset.mem_filter] at hSF
  refine ⟨S, hSF.2, ?_⟩
  intro T hT
  exact hmax T (by rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ T, hT⟩)

/-- For a maximum-cardinality induced matching, any edge outside `S` is either line-graph adjacent to an
`S`-edge, or shares a line-graph neighbour with one. -/
lemma max_step {S : Finset G.edgeSet} (hS : Ind S)
    (hmax : ∀ T : Finset G.edgeSet, Ind T → T.card ≤ S.card)
    {e : G.edgeSet} (he : e ∉ S) :
    (∃ f ∈ S, G.lineGraph.Adj e f) ∨ (∃ f ∈ S, ∃ g, G.lineGraph.Adj e g ∧ G.lineGraph.Adj f g) := by
  have hnot : ¬ Ind (insert e S) := by
    intro h
    have hle := hmax (insert e S) h
    rw [Finset.card_insert_of_notMem he] at hle
    omega
  unfold Ind at hnot
  push_neg at hnot
  obtain ⟨e', he', f', hf', hne', hdisj⟩ := hnot
  rw [Finset.mem_insert] at he' hf'
  rcases he' with heq | he'S
  · subst e'
    rcases hf' with heq2 | hf'S
    · subst f'
      exact absurd rfl hne'
    · by_cases hadj : G.lineGraph.Adj e f'
      · exact Or.inl ⟨f', hf'S, hadj⟩
      · exact Or.inr ⟨f', hf'S, hdisj hadj⟩
  · rcases hf' with heq2 | hf'S
    · subst f'
      by_cases hadj : G.lineGraph.Adj e' e
      · exact Or.inl ⟨e', he'S, hadj.symm⟩
      · obtain ⟨g, h1, h2⟩ := hdisj hadj
        exact Or.inr ⟨e', he'S, g, h2, h1⟩
    · by_cases hadj : G.lineGraph.Adj e' f'
      · exact absurd hadj (hS e' he'S f' hf'S hne').1
      · obtain ⟨g, h1, h2⟩ := hdisj hadj
        exact absurd ⟨g, h1, h2⟩ (hS e' he'S f' hf'S hne').2

end op309_cubic_induced_matching_total_dominating_cut

theorem op309_cubic_induced_matching_total_dominating_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdegree : ∀ v, G.degree v = 3) :
    ∃ S : Finset G.edgeSet,
      (∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ¬ G.lineGraph.Adj e f ∧ ¬ ∃ g, G.lineGraph.Adj e g ∧ G.lineGraph.Adj f g) ∧
      ∀ e : G.edgeSet, ∃ f : G.edgeSet, G.lineGraph.Adj e f ∧
        ∃ u v : V, f.1 = s(u,v) ∧
          ((∃ g ∈ S, u ∈ g.1) ∧ ¬ (∃ g ∈ S, v ∈ g.1) ∨
           (∃ g ∈ S, v ∈ g.1) ∧ ¬ (∃ g ∈ S, u ∈ g.1)) := by
  classical
  obtain ⟨S, hS, hmax⟩ := op309_cubic_induced_matching_total_dominating_cut.exists_max_induced (G := G)
  refine ⟨S, hS, ?_⟩
  intro e
  obtain ⟨a, b, hab⟩ := op309_cubic_induced_matching_total_dominating_cut.sym2_exists_pair (e : Sym2 V)
  have hae : a ∈ (e : Sym2 V) := by rw [hab]; exact Sym2.mem_mk_left a b
  have hbe : b ∈ (e : Sym2 V) := by rw [hab]; exact Sym2.mem_mk_right a b
  by_cases hca : op309_cubic_induced_matching_total_dominating_cut.Cov S a
  · obtain ⟨f, hfe, haf, c, hfc, hcc⟩ := op309_cubic_induced_matching_total_dominating_cut.exists_cut_at hS (hdegree a) hca hae
    refine ⟨f, ?_, a, c, hfc, Or.inl ⟨hca, hcc⟩⟩
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨hfe.symm, a, hae, haf⟩
  · by_cases hcb : op309_cubic_induced_matching_total_dominating_cut.Cov S b
    · obtain ⟨f, hfe, hbf, c, hfc, hcc⟩ := op309_cubic_induced_matching_total_dominating_cut.exists_cut_at hS (hdegree b) hcb hbe
      refine ⟨f, ?_, b, c, hfc, Or.inl ⟨hcb, hcc⟩⟩
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨hfe.symm, b, hbe, hbf⟩
    · have he : e ∉ S := fun heS => hca ⟨e, heS, hae⟩
      rcases op309_cubic_induced_matching_total_dominating_cut.max_step hS hmax he with ⟨f, hfS, hAdj⟩ | ⟨f, hfS, g, hge, hgf⟩
      · obtain ⟨hne, v, hve, hvf⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hAdj
        have hcv : ¬ op309_cubic_induced_matching_total_dominating_cut.Cov S v := by
          intro hcvv
          rw [hab, Sym2.mem_iff] at hve
          rcases hve with hva | hvb
          · rw [hva] at hcvv; exact hca hcvv
          · rw [hvb] at hcvv; exact hcb hcvv
        exact absurd ⟨f, hfS, hvf⟩ hcv
      · obtain ⟨hne1, v, hve, hvg⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hge
        obtain ⟨hne2, w, hwf, hwg⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hgf
        have hcv : ¬ op309_cubic_induced_matching_total_dominating_cut.Cov S v := by
          intro hcvv
          rw [hab, Sym2.mem_iff] at hve
          rcases hve with hva | hvb
          · rw [hva] at hcvv; exact hca hcvv
          · rw [hvb] at hcvv; exact hcb hcvv
        have hcw : op309_cubic_induced_matching_total_dominating_cut.Cov S w := ⟨f, hfS, hwf⟩
        have hvw : v ≠ w := fun h => hcv (h ▸ hcw)
        have hgeq : (g : Sym2 V) = s(v, w) := op309_cubic_induced_matching_total_dominating_cut.sym2_eq_of_mem hvg hwg hvw
        refine ⟨g, hge, v, w, hgeq, Or.inr ⟨hcw, hcv⟩⟩
