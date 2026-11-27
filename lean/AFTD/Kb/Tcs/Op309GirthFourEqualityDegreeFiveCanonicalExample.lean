import AFTD.Prelude
import AFTD.Kb.Tcs.Op309UncoloredAlmostStarForest
import AFTD.Kb.Tcs.Op309PaddedAlmostStarPortGraphValid
import AFTD.Kb.Tcs.Op309GraphFourDegenerate
import AFTD.Kb.Tcs.Op309PaddedBoundaryPort
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.G

/-!
# op309_girth_four_equality_degree_five_canonical_example

Topic: graphs   Node: f3ae59d7e92a

Provenance: helper lemma. OP-309; experiments 42137, 42138 and 42140 give the explicit girth-four canonical equality counterexample.

The displayed connected triangle-free cubic fourteen-vertex graph has a totally dominating P3 forest with five uncovered vertices and a valid canonical port quotient of maximum degree at most five that is four-degenerate.
-/

def in1251_L : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 9), (1, 7), (1, 8), (1, 10), (2, 7), (2, 8), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 13)]

def in1251_G : SimpleGraph (Fin 14) where
  Adj u v := (u.val, v.val) ∈ in1251_L ∨ (v.val, u.val) ∈ in1251_L
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance in1251_inst : DecidableRel in1251_G.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val, v.val) ∈ in1251_L ∨ (v.val, u.val) ∈ in1251_L))

def in1251_ed (a b : Fin 14) (h : in1251_G.Adj a b := by decide) : in1251_G.edgeSet := ⟨s(a, b), h⟩

def in1251_Ef : Fin 21 → in1251_G.edgeSet := ![in1251_ed 0 7, in1251_ed 0 8, in1251_ed 0 9, in1251_ed 1 7, in1251_ed 1 8, in1251_ed 1 10, in1251_ed 2 7, in1251_ed 2 8, in1251_ed 2 12, in1251_ed 3 9, in1251_ed 3 10, in1251_ed 3 11, in1251_ed 4 9, in1251_ed 4 11, in1251_ed 4 13, in1251_ed 5 10, in1251_ed 5 12, in1251_ed 5 13, in1251_ed 6 11, in1251_ed 6 12, in1251_ed 6 13]

theorem in1251_Ef_complete (e : in1251_G.edgeSet) : ∃ i, in1251_Ef i = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
  have key : ∀ a b : Fin 14, in1251_G.Adj a b → ∃ i, (in1251_Ef i).1 = s(a, b) := by decide
  obtain ⟨i, hi⟩ := key a b he
  exact ⟨i, Subtype.ext hi⟩

def in1251_R : Finset in1251_G.edgeSet :=
  {in1251_ed 1 7, in1251_ed 1 8, in1251_ed 3 9, in1251_ed 3 11, in1251_ed 5 12, in1251_ed 5 13}

def in1251_QL : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 5), (2, 6), (2, 7), (3, 5), (3, 8), (4, 6), (4, 7), (4, 8), (5, 6), (5, 8), (6, 7), (7, 8)]

def in1251_Q : SimpleGraph (Fin 9) where
  Adj u v := (u.val, v.val) ∈ in1251_QL ∨ (v.val, u.val) ∈ in1251_QL
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance in1251_Qinst : DecidableRel in1251_Q.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val, v.val) ∈ in1251_QL ∨ (v.val, u.val) ∈ in1251_QL))

def in1251_TL : List ((ℕ × ℕ) × ℕ) := [((0, 7), 0), ((2, 8), 0), ((0, 8), 1), ((2, 7), 1), ((0, 9), 2), ((4, 11), 2), ((1, 10), 3), ((2, 12), 4), ((6, 13), 4), ((3, 10), 5), ((4, 9), 6), ((6, 11), 6), ((4, 13), 7), ((6, 12), 7), ((5, 10), 8)]

def in1251_qt (a b : Fin 14) : Fin 9 :=
  ⟨((in1251_TL.lookup (min a.val b.val, max a.val b.val)).getD 0) % 9, Nat.mod_lt _ (by norm_num)⟩

def in1251_qs : Sym2 (Fin 14) → Fin 9 :=
  Sym2.lift ⟨in1251_qt, fun a b => by simp only [in1251_qt, min_comm, max_comm]⟩

def in1251_q : Sum in1251_G.edgeSet (Fin 14 × Fin 3) → Fin 9
  | .inl e => in1251_qs e.1
  | .inr _ => 0

theorem in1251_deg3 : ∀ v, in1251_G.degree v = 3 := by decide

theorem in1251_port (v : Fin 14) (p : Sum in1251_G.edgeSet (Fin 14 × Fin 3))
    (h : op309_padded_boundary_port in1251_G in1251_R v p) :
    ∃ i, p = .inl (in1251_Ef i) ∧ in1251_Ef i ∉ in1251_R ∧ v ∈ (in1251_Ef i).1 := by
  cases p with
  | inl e =>
    obtain ⟨i, rfl⟩ := in1251_Ef_complete e
    exact ⟨i, rfl, h.1, h.2⟩
  | inr wj =>
    obtain ⟨w, j⟩ := wj
    have h2 := h.2
    rw [in1251_deg3] at h2
    omega

theorem in1251_triples : ∀ a b c : Fin 14, [a,b,c].Nodup →
    s(a,b) ∈ in1251_R.image Subtype.val → s(b,c) ∈ in1251_R.image Subtype.val →
    (in1251_R.filter fun e => a ∈ e.1).card = 1 → (in1251_R.filter fun e => b ∈ e.1).card = 2 →
    (in1251_R.filter fun e => c ∈ e.1).card = 1 →
    (a, b, c) ∈ ([(7, 1, 8), (8, 1, 7), (9, 3, 11), (11, 3, 9), (12, 5, 13), (13, 5, 12)] : List (Fin 14 × Fin 14 × Fin 14)) := by
  decide

set_option synthInstance.maxSize 200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem in1251_p3 : ∀ a b c : Fin 14, (a, b, c) ∈ ([(7,1,8),(8,1,7),(9,3,11),(11,3,9),(12,5,13),(13,5,12)] : List (Fin 14 × Fin 14 × Fin 14)) →
    ∀ ia : Fin 21, in1251_Ef ia ∉ in1251_R → a ∈ (in1251_Ef ia).1 →
    ∀ ia' : Fin 21, in1251_Ef ia' ∉ in1251_R → a ∈ (in1251_Ef ia').1 → ia ≠ ia' →
    ∀ ib : Fin 21, in1251_Ef ib ∉ in1251_R → b ∈ (in1251_Ef ib).1 →
    ∀ ic : Fin 21, in1251_Ef ic ∉ in1251_R → c ∈ (in1251_Ef ic).1 →
    ∀ ic' : Fin 21, in1251_Ef ic' ∉ in1251_R → c ∈ (in1251_Ef ic').1 → ic ≠ ic' →
      ((in1251_qs (in1251_Ef ia).1 = in1251_qs (in1251_Ef ic).1 ∧
          in1251_qs (in1251_Ef ia').1 = in1251_qs (in1251_Ef ic').1) ∨
        (in1251_qs (in1251_Ef ia).1 = in1251_qs (in1251_Ef ic').1 ∧
          in1251_qs (in1251_Ef ia').1 = in1251_qs (in1251_Ef ic).1)) ∧
      [in1251_qs (in1251_Ef ib).1, in1251_qs (in1251_Ef ia).1, in1251_qs (in1251_Ef ia').1].Pairwise
        in1251_Q.Adj := by
  decide +kernel

theorem in1251_conn : in1251_G.Connected := by
  have r : ∀ a b : Fin 14, in1251_G.Adj a b → in1251_G.Reachable a b := fun a b h => h.reachable
  have h0 : ∀ v, in1251_G.Reachable 0 v := by
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl _
    · exact (r 0 7 (by decide)) |>.trans (r 7 1 (by decide))
    · exact (r 0 7 (by decide)) |>.trans (r 7 2 (by decide))
    · exact (r 0 9 (by decide)) |>.trans (r 9 3 (by decide))
    · exact (r 0 9 (by decide)) |>.trans (r 9 4 (by decide))
    · exact (r 0 7 (by decide)) |>.trans (r 7 1 (by decide)) |>.trans (r 1 10 (by decide)) |>.trans (r 10 5 (by decide))
    · exact (r 0 7 (by decide)) |>.trans (r 7 2 (by decide)) |>.trans (r 2 12 (by decide)) |>.trans (r 12 6 (by decide))
    · exact (r 0 7 (by decide))
    · exact (r 0 8 (by decide))
    · exact (r 0 9 (by decide))
    · exact (r 0 7 (by decide)) |>.trans (r 7 1 (by decide)) |>.trans (r 1 10 (by decide))
    · exact (r 0 9 (by decide)) |>.trans (r 9 3 (by decide)) |>.trans (r 3 11 (by decide))
    · exact (r 0 7 (by decide)) |>.trans (r 7 2 (by decide)) |>.trans (r 2 12 (by decide))
    · exact (r 0 9 (by decide)) |>.trans (r 9 4 (by decide)) |>.trans (r 4 13 (by decide))
  exact ⟨fun u v => (h0 u).symm.trans (h0 v)⟩

theorem in1251_girth : (4 : ℕ∞) ≤ in1251_G.egirth := by
  have notri : ∀ a b c : Fin 14, in1251_G.Adj a b → in1251_G.Adj b c → in1251_G.Adj c a → False := by
    decide
  rw [SimpleGraph.le_egirth]
  intro a w hw
  have h3 := hw.three_le_length
  suffices h : 4 ≤ w.length by exact_mod_cast h
  by_contra hlt
  have hl : w.length = 3 := by omega
  have e1 := w.adj_getVert_succ (i := 0) (by omega)
  have e2 := w.adj_getVert_succ (i := 1) (by omega)
  have e3 := w.adj_getVert_succ (i := 2) (by omega)
  have g0 : w.getVert 0 = a := w.getVert_zero
  have g3 : w.getVert 3 = a := by rw [← hl]; exact w.getVert_length
  rw [g0] at e1
  rw [show (2 : ℕ) + 1 = 3 from rfl, g3] at e3
  exact notri _ _ _ e1 e2 e3

theorem in1251_ncard (v : Fin 14) : (in1251_G.neighborSet v).ncard = 3 := by
  rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset,
    SimpleGraph.card_neighborFinset_eq_degree, in1251_deg3]

set_option synthInstance.maxSize 200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem in1251_forest : op309_uncolored_almost_star_forest in1251_G in1251_R := by
  unfold op309_uncolored_almost_star_forest
  simp only [SimpleGraph.lineGraph_adj_iff_exists]
  decide +kernel

theorem in1251_deg_le : ∀ v, (in1251_R.filter fun e => v ∈ e.1).card ≤ 2 := by decide

theorem in1251_nop4 : ∀ e ∈ in1251_R, ¬ ∃ a b : Fin 14, e.1 = s(a,b) ∧
    (in1251_R.filter fun f => a ∈ f.1).card = 2 ∧ (in1251_R.filter fun f => b ∈ f.1).card = 2 := by
  decide +kernel

theorem in1251_dom : ∀ e : in1251_G.edgeSet, ∃ f ∈ in1251_R, in1251_G.lineGraph.Adj e f := by
  intro e
  obtain ⟨i, rfl⟩ := in1251_Ef_complete e
  simp only [SimpleGraph.lineGraph_adj_iff_exists]
  revert i
  decide +kernel

theorem in1251_unc : (Finset.univ.filter fun v : Fin 14 => ∀ e ∈ in1251_R, v ∉ e.1).card = 5 := by
  decide +kernel

theorem in1251_c1 : ∀ v : Fin 14, (in1251_R.filter fun e => v ∈ e.1).card = 0 →
    ∀ i j : Fin 21, in1251_Ef i ∉ in1251_R → in1251_Ef j ∉ in1251_R → v ∈ (in1251_Ef i).1 →
      v ∈ (in1251_Ef j).1 → i ≠ j → in1251_Q.Adj (in1251_qs (in1251_Ef i).1) (in1251_qs (in1251_Ef j).1) := by
  decide +kernel

theorem in1251_nobb : ∀ b c : Fin 14, s(b,c) ∈ in1251_R.image Subtype.val →
    (in1251_R.filter fun e => b ∈ e.1).card = 2 → (in1251_R.filter fun e => c ∈ e.1).card = 2 → False := by
  decide +kernel

theorem in1251_degen : ∀ S : Finset (Fin 9), S.Nonempty → ∃ v ∈ S, (S.filter (in1251_Q.Adj v)).card ≤ 4 := by
  decide +kernel

theorem in1251_Qdeg : ∀ v : Fin 9, (in1251_Q.neighborFinset v).card ≤ 5 := by decide

set_option synthInstance.maxSize 200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem in1251_canon : ∀ i j : Fin 21, in1251_Ef i ∉ in1251_R → in1251_Ef j ∉ in1251_R →
    in1251_qs (in1251_Ef i).1 = in1251_qs (in1251_Ef j).1 →
    i = j ∨ ∃ a b c : Fin 14, [a,b,c].Nodup ∧
      s(a,b) ∈ in1251_R.image Subtype.val ∧ s(b,c) ∈ in1251_R.image Subtype.val ∧
      (in1251_R.filter fun g => a ∈ g.1).card = 1 ∧
      (in1251_R.filter fun g => b ∈ g.1).card = 2 ∧
      (in1251_R.filter fun g => c ∈ g.1).card = 1 ∧
      ((a ∈ (in1251_Ef i).1 ∧ c ∈ (in1251_Ef j).1) ∨ (c ∈ (in1251_Ef i).1 ∧ a ∈ (in1251_Ef j).1)) := by
  decide +kernel

theorem op309_girth_four_equality_degree_five_canonical_example
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hG : ∀ u v : Fin 14, G.Adj u v ↔
      ((u.val,v.val) ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 8), (1, 10), (2, 7), (2, 8), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 13)] : List (ℕ × ℕ)) ∨
       (v.val,u.val) ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 8), (1, 10), (2, 7), (2, 8), (2, 12), (3, 9), (3, 10), (3, 11), (4, 9), (4, 11), (4, 13), (5, 10), (5, 12), (5, 13), (6, 11), (6, 12), (6, 13)] : List (ℕ × ℕ)))) :
    G.Connected ∧ (∀ v, (G.neighborSet v).ncard = 3) ∧ (4 : ℕ∞) ≤ G.egirth ∧
    ∃ R : Finset G.edgeSet,
      op309_uncolored_almost_star_forest G R ∧
      (∀ v, (R.filter fun e => v ∈ e.1).card ≤ 2) ∧
      (∀ e ∈ R, ¬ ∃ a b : Fin 14, e.1 = s(a,b) ∧
        (R.filter fun f => a ∈ f.1).card = 2 ∧
        (R.filter fun f => b ∈ f.1).card = 2) ∧
      (∀ e : G.edgeSet, ∃ f ∈ R, G.lineGraph.Adj e f) ∧
      (Finset.univ.filter fun v : Fin 14 => ∀ e ∈ R, v ∉ e.1).card = 5 ∧
      ∃ (Q : SimpleGraph (Fin 9)) (q : Sum G.edgeSet (Fin 14 × Fin 3) → Fin 9),
        op309_padded_almost_star_port_graph_valid G R Q q ∧
        op309_graph_four_degenerate Q ∧
        (∀ v, (Q.neighborSet v).ncard ≤ 5) ∧
        (∀ e f : G.edgeSet, e ∉ R → f ∉ R → q (.inl e) = q (.inl f) →
          e = f ∨ ∃ a b c : Fin 14, [a,b,c].Nodup ∧
            s(a,b) ∈ R.image Subtype.val ∧ s(b,c) ∈ R.image Subtype.val ∧
            (R.filter fun g => a ∈ g.1).card = 1 ∧
            (R.filter fun g => b ∈ g.1).card = 2 ∧
            (R.filter fun g => c ∈ g.1).card = 1 ∧
            ((a ∈ e.1 ∧ c ∈ f.1) ∨ (c ∈ e.1 ∧ a ∈ f.1))) := by
  have hGe : G = in1251_G := by
    ext u v
    rw [hG]
    rfl
  subst hGe
  have hi : ‹DecidableRel in1251_G.Adj› = in1251_inst := Subsingleton.elim _ _
  subst hi
  refine ⟨in1251_conn, in1251_ncard, in1251_girth, in1251_R, in1251_forest, in1251_deg_le,
    in1251_nop4, in1251_dom, in1251_unc, in1251_Q, in1251_q, ?_, ?_, ?_, ?_⟩
  · dsimp only [op309_padded_almost_star_port_graph_valid]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv e f he hf hve hvf hef
      obtain ⟨i, rfl⟩ := in1251_Ef_complete e
      obtain ⟨j, rfl⟩ := in1251_Ef_complete f
      exact in1251_c1 v hv i j he hf hve hvf (fun h => hef (by rw [h]))
    · intro a b c hnd hab hbc ha hb hc ea ea' eb ec ec' pa pa' hne pb pc pc' hne'
      have hT := in1251_triples a b c hnd hab hbc ha hb hc
      obtain ⟨ia, rfl, na, va⟩ := in1251_port a ea pa
      obtain ⟨ia', rfl, na', va'⟩ := in1251_port a ea' pa'
      obtain ⟨ib, rfl, nb, vb⟩ := in1251_port b eb pb
      obtain ⟨ic, rfl, nc, vc⟩ := in1251_port c ec pc
      obtain ⟨ic', rfl, nc', vc'⟩ := in1251_port c ec' pc'
      exact in1251_p3 a b c hT ia na va ia' na' va' (fun h => hne (by rw [h])) ib nb vb
        ic nc vc ic' nc' vc' (fun h => hne' (by rw [h]))
    · intro a b c d _ _ hbc _ _ hb hc
      exact (in1251_nobb b c hbc hb hc).elim
    · intro x a b d _ _ _ _ hx
      have := in1251_deg_le x
      omega
  · intro S hS
    obtain ⟨v, hv, hc⟩ := in1251_degen S hS
    exact ⟨v, hv, S.filter (in1251_Q.Adj v), hc, fun w hw hvw => Finset.mem_filter.2 ⟨hw, hvw⟩⟩
  · intro v
    rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset]
    exact in1251_Qdeg v
  · intro e f he hf hq
    obtain ⟨i, rfl⟩ := in1251_Ef_complete e
    obtain ⟨j, rfl⟩ := in1251_Ef_complete f
    rcases in1251_canon i j he hf hq with h | h
    · left; rw [h]
    · right; exact h
