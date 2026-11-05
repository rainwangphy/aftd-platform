import AFTD.Prelude
import AFTD.Kb.Tcs.RandicIndex

/-!
# op1012_randic_index_le_half_card

Topic: graphs   Node: 4a6c47a44d81

Provenance: formalization of a published result. Source: arXiv:2611.03879 Lemma 14

For any finite simple graph G on a finite vertex type V, its Randić index is at most half the number of vertices: randic_index G ≤ (Fintype.card V : ℝ) / 2.
-/

open Finset

private lemma op1012_randic_index_le_half_card_amgm_term (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 / Real.sqrt ((a:ℝ) * (b:ℝ)) ≤ (1/2) * (1/(a:ℝ) + 1/(b:ℝ)) := by
  have ha' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have key : (1/Real.sqrt (a:ℝ)) * (1/Real.sqrt (b:ℝ)) ≤
      (1/2) * ((1/Real.sqrt (a:ℝ))^2 + (1/Real.sqrt (b:ℝ))^2) := by
    nlinarith [sq_nonneg ((1:ℝ)/Real.sqrt (a:ℝ) - (1:ℝ)/Real.sqrt (b:ℝ))]
  have ha2 : (1/Real.sqrt (a:ℝ))^2 = 1/(a:ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt ha'.le]
  have hb2 : (1/Real.sqrt (b:ℝ))^2 = 1/(b:ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hb'.le]
  have hmul : (1:ℝ)/Real.sqrt ((a:ℝ)*(b:ℝ)) = (1/Real.sqrt (a:ℝ)) * (1/Real.sqrt (b:ℝ)) := by
    rw [Real.sqrt_mul ha'.le, one_div_mul_one_div]
  rw [hmul, ← ha2, ← hb2]
  exact key

attribute [local instance] Classical.propDecidable in
private lemma op1012_randic_index_le_half_card_two_mul_edge_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → V → ℝ) (hf : ∀ a b, f a b = f b a) :
    2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨f, hf⟩ e = ∑ d : G.Dart, f d.fst d.snd := by
  classical
  have hinner : ∀ e ∈ G.edgeFinset,
      ∑ d ∈ (univ : Finset G.Dart).filter (fun d => d.edge = e), f d.fst d.snd
        = 2 * Sym2.lift ⟨f, hf⟩ e := by
    intro e
    induction e using Sym2.ind with
    | h u v =>
      intro he
      have hadde : G.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        exact (SimpleGraph.mem_edgeFinset).1 he
      let d0 : G.Dart := ⟨(u, v), hadde⟩
      have hfilter : (univ : Finset G.Dart).filter (fun d => d.edge = s(u, v)) = {d0, d0.symm} :=
        SimpleGraph.Dart.edge_fiber d0
      rw [hfilter, Finset.sum_pair (SimpleGraph.Dart.symm_ne d0).symm]
      rw [Sym2.lift_mk]
      show f u v + f v u = 2 * f u v
      rw [hf v u]
      ring
  calc 2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨f, hf⟩ e
      = ∑ e ∈ G.edgeFinset, 2 * Sym2.lift ⟨f, hf⟩ e := by rw [Finset.mul_sum]
    _ = ∑ e ∈ G.edgeFinset, ∑ d ∈ (univ : Finset G.Dart).filter (fun d => d.edge = e),
          f d.fst d.snd := by
        refine Finset.sum_congr rfl ?_
        intro e he
        rw [hinner e he]
    _ = ∑ d : G.Dart, f d.fst d.snd := by
        rw [Finset.sum_congr rfl (fun e he => Finset.sum_filter _ _), Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro d _
        rw [Finset.sum_ite_eq]
        simp [SimpleGraph.Dart.edge_mem]

attribute [local instance] Classical.propDecidable in
private lemma op1012_randic_index_le_half_card_sum_dart_fst {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a : V → ℝ) :
    ∑ d : G.Dart, a d.fst = ∑ v, (G.degree v : ℝ) * a v := by
  classical
  let ee : G.Dart ≃ Σ v : V, G.neighborSet v :=
    { toFun := fun d => ⟨d.fst, ⟨d.snd, d.adj⟩⟩
      invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
      left_inv := by intro d; rfl
      right_inv := by intro s; rfl }
  rw [Fintype.sum_equiv ee (fun d : G.Dart => a d.fst) (fun s => a s.1) (by intro d; rfl)]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro v _
  have hc : (∑ y : G.neighborSet v, a ((⟨v, y⟩ : Σ w : V, G.neighborSet w).fst))
      = ∑ _y : G.neighborSet v, a v :=
    Finset.sum_congr rfl (fun y _ => rfl)
  rw [hc]
  rw [show (∑ _y : G.neighborSet v, a v) = (Fintype.card (G.neighborSet v) : ℝ) * a v from by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  rw [SimpleGraph.card_neighborSet_eq_degree]

attribute [local instance] Classical.propDecidable in
private lemma op1012_randic_index_le_half_card_sum_dart_snd {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a : V → ℝ) :
    ∑ d : G.Dart, a d.snd = ∑ d : G.Dart, a d.fst := by
  classical
  let σ : G.Dart ≃ G.Dart :=
    { toFun := SimpleGraph.Dart.symm
      invFun := SimpleGraph.Dart.symm
      left_inv := fun d => SimpleGraph.Dart.symm_symm d
      right_inv := fun d => SimpleGraph.Dart.symm_symm d }
  have h := Equiv.sum_comp σ (fun d : G.Dart => a d.fst)
  simpa [σ] using h

attribute [local instance] Classical.propDecidable in
/-- Upper bound on the Randić index: for any finite simple graph G, R(G) ≤ |V| / 2. -/
theorem op1012_randic_index_le_half_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    randic_index G ≤ (Fintype.card V : ℝ) / 2 := by
  classical
  have hdef : randic_index G = ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => 1/Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ)),
        by intro a b; simp only [mul_comm]⟩ e := rfl
  rw [hdef]
  have step1 : ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => 1/Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ)),
          by intro a b; simp only [mul_comm]⟩ e
      ≤ ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (1/2) * (1/(G.degree u : ℝ) + 1/(G.degree v : ℝ)),
          by intro a b; simp only [add_comm]⟩ e := by
    refine Finset.sum_le_sum ?_
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.lift_mk, Sym2.lift_mk]
      have hadde : G.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        exact (SimpleGraph.mem_edgeFinset).1 he
      have hu : 1 ≤ G.degree u := (SimpleGraph.degree_pos_iff_exists_adj G u).mpr ⟨v, hadde⟩
      have hv : 1 ≤ G.degree v := (SimpleGraph.degree_pos_iff_exists_adj G v).mpr ⟨u, hadde.symm⟩
      exact op1012_randic_index_le_half_card_amgm_term (G.degree u) (G.degree v) hu hv
  have step2 := op1012_randic_index_le_half_card_two_mul_edge_sum G
    (fun u v => (1/2) * (1/(G.degree u : ℝ) + 1/(G.degree v : ℝ)))
    (by intro a b; simp only [add_comm])
  have step3 : ∑ d : G.Dart, (1/2) * (1/(G.degree d.fst : ℝ) + 1/(G.degree d.snd : ℝ))
      = ∑ d : G.Dart, 1/(G.degree d.fst : ℝ) := by
    have hsplit : ∀ d : G.Dart, (1/2) * (1/(G.degree d.fst : ℝ) + 1/(G.degree d.snd : ℝ))
        = (1/2) * (1/(G.degree d.fst : ℝ)) + (1/2) * (1/(G.degree d.snd : ℝ)) := fun d => by ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [op1012_randic_index_le_half_card_sum_dart_snd G (fun v => 1/(G.degree v : ℝ))]
    ring
  have step4 : ∑ d : G.Dart, 1/(G.degree d.fst : ℝ) ≤ (Fintype.card V : ℝ) := by
    rw [op1012_randic_index_le_half_card_sum_dart_fst G (fun v => 1/(G.degree v : ℝ))]
    have hterm : ∀ v, (G.degree v : ℝ) * (1/(G.degree v : ℝ)) ≤ 1 := by
      intro v
      by_cases hv : G.degree v = 0
      · simp [hv]
      · have hv' : (G.degree v : ℝ) ≠ 0 := by exact_mod_cast hv
        rw [mul_one_div, div_self hv']
    calc ∑ v, (G.degree v : ℝ) * (1/(G.degree v : ℝ)) ≤ ∑ _v : V, (1:ℝ) :=
          Finset.sum_le_sum (fun v _ => hterm v)
      _ = (Fintype.card V : ℝ) := by simp
  have hB : ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (1/2) * (1/(G.degree u : ℝ) + 1/(G.degree v : ℝ)),
          by intro a b; simp only [add_comm]⟩ e
      = (1/2) * ∑ d : G.Dart, (1/2) * (1/(G.degree d.fst : ℝ) + 1/(G.degree d.snd : ℝ)) := by
    linarith [step2]
  linarith [step1, hB, step3, step4]
