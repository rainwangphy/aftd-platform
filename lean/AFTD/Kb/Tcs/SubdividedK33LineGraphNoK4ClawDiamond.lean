import AFTD.Prelude
import AFTD.Kb.Tcs.HSubdividedK33
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Tcs.IsDiamondFree
import AFTD.Kb.Tcs.DiamondGraph

/-!
# subdivided_k33_line_graph_no_k4_claw_diamond

Topic: graphs   Node: e4ad4d756089

Provenance: helper lemma. Helper for arXiv:2610.32404 Proposition 11.2 (PR-412).

The line graph of the once-subdivided K3,3 has no induced K4, claw, or diamond.
-/

theorem sk33_line_common_vertex {V : Type*} (H : SimpleGraph V)
    (htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj x z → False)
    (e1 e2 e3 : Sym2 V) (h1 : e1 ∈ H.edgeSet) (h2 : e2 ∈ H.edgeSet) (h3 : e3 ∈ H.edgeSet)
    (a12 : ∃ v, v ∈ e1 ∧ v ∈ e2) (a13 : ∃ v, v ∈ e1 ∧ v ∈ e3)
    (a23 : ∃ v, v ∈ e2 ∧ v ∈ e3) :
    ∃ x, x ∈ e1 ∧ x ∈ e2 ∧ x ∈ e3 := by
  obtain ⟨p, p1, p2⟩ := a12
  obtain ⟨q, q1, q3⟩ := a13
  obtain ⟨r, r2, r3⟩ := a23
  by_cases hpq : p = q
  · subst hpq; exact ⟨p, p1, p2, q3⟩
  by_cases hpr : p = r
  · subst hpr; exact ⟨p, p1, p2, r3⟩
  by_cases hqr : q = r
  · subst hqr; exact ⟨q, q1, r2, q3⟩
  exfalso
  have E1 : e1 = s(p, q) := (Sym2.mem_and_mem_iff hpq).1 ⟨p1, q1⟩
  have E2 : e2 = s(p, r) := (Sym2.mem_and_mem_iff hpr).1 ⟨p2, r2⟩
  have E3 : e3 = s(q, r) := (Sym2.mem_and_mem_iff hqr).1 ⟨q3, r3⟩
  subst E1 E2 E3
  exact htri p q r ((SimpleGraph.mem_edgeSet H).1 h1) ((SimpleGraph.mem_edgeSet H).1 h3)
    ((SimpleGraph.mem_edgeSet H).1 h2)

theorem sk33_line_no_four {V : Type*} (H : SimpleGraph V)
    (htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj x z → False)
    (hdeg : ∀ x a b c d, H.Adj x a → H.Adj x b → H.Adj x c → H.Adj x d →
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d)
    (e1 e2 e3 e4 : Sym2 V) (h1 : e1 ∈ H.edgeSet) (h2 : e2 ∈ H.edgeSet) (h3 : e3 ∈ H.edgeSet)
    (h4 : e4 ∈ H.edgeSet)
    (n12 : e1 ≠ e2) (n13 : e1 ≠ e3) (n14 : e1 ≠ e4) (n23 : e2 ≠ e3) (n24 : e2 ≠ e4)
    (n34 : e3 ≠ e4)
    (a12 : ∃ v, v ∈ e1 ∧ v ∈ e2) (a13 : ∃ v, v ∈ e1 ∧ v ∈ e3)
    (a23 : ∃ v, v ∈ e2 ∧ v ∈ e3) (a24 : ∃ v, v ∈ e2 ∧ v ∈ e4)
    (a34 : ∃ v, v ∈ e3 ∧ v ∈ e4) : False := by
  obtain ⟨x, x1, x2, x3⟩ := sk33_line_common_vertex H htri e1 e2 e3 h1 h2 h3 a12 a13 a23
  obtain ⟨y, y2, y3, y4⟩ := sk33_line_common_vertex H htri e2 e3 e4 h2 h3 h4 a23 a24 a34
  have hxy : x = y := by
    by_contra h
    exact n23 (((Sym2.mem_and_mem_iff h).1 ⟨x2, y2⟩).trans
      ((Sym2.mem_and_mem_iff h).1 ⟨x3, y3⟩).symm)
  subst hxy
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.1 x1
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 x2
  obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.1 x3
  obtain ⟨d, rfl⟩ := Sym2.mem_iff_exists.1 y4
  rw [SimpleGraph.mem_edgeSet] at h1 h2 h3 h4
  rcases hdeg x a b c d h1 h2 h3 h4 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem sk33_line_no_claw {V : Type*} (e0 f1 f2 f3 : Sym2 V)
    (a1 : ∃ v, v ∈ e0 ∧ v ∈ f1) (a2 : ∃ v, v ∈ e0 ∧ v ∈ f2) (a3 : ∃ v, v ∈ e0 ∧ v ∈ f3)
    (b12 : ¬ ∃ v, v ∈ f1 ∧ v ∈ f2) (b13 : ¬ ∃ v, v ∈ f1 ∧ v ∈ f3)
    (b23 : ¬ ∃ v, v ∈ f2 ∧ v ∈ f3) : False := by
  induction e0 using Sym2.ind with
  | h a b =>
    obtain ⟨v1, hv1, w1⟩ := a1
    obtain ⟨v2, hv2, w2⟩ := a2
    obtain ⟨v3, hv3, w3⟩ := a3
    rw [Sym2.mem_iff] at hv1 hv2 hv3
    rcases hv1 with e1 | e1 <;> rcases hv2 with e2 | e2 <;> rcases hv3 with e3 | e3 <;>
      subst e1 e2 e3 <;>
      first
      | exact b12 ⟨_, w1, w2⟩
      | exact b13 ⟨_, w1, w3⟩
      | exact b23 ⟨_, w2, w3⟩

def sk33_adjB (x y : Fin 7) : Bool :=
  [(0, 6), (6, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)].any
    (fun p : ℕ × ℕ => (p.1 == x.val && p.2 == y.val) || (p.2 == x.val && p.1 == y.val))

theorem sk33_adj_iff (x y : Fin 7) : h_subdivided_k33.Adj x y ↔ sk33_adjB x y = true := by
  fin_cases x <;> fin_cases y <;> simp [h_subdivided_k33, sk33_adjB]

theorem sk33_tri : ∀ x y z, h_subdivided_k33.Adj x y → h_subdivided_k33.Adj y z →
    h_subdivided_k33.Adj x z → False := by
  simp only [sk33_adj_iff]; decide

theorem sk33_deg : ∀ x a b c d, h_subdivided_k33.Adj x a → h_subdivided_k33.Adj x b →
    h_subdivided_k33.Adj x c → h_subdivided_k33.Adj x d →
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  simp only [sk33_adj_iff]; decide

theorem subdivided_k33_line_graph_no_k4_claw_diamond :
    (¬ SimpleGraph.IsIndContained (⊤ : SimpleGraph (Fin 4)) h_subdivided_k33.lineGraph) ∧
    IsClawFree h_subdivided_k33.lineGraph ∧ is_diamond_free h_subdivided_k33.lineGraph := by
  have adj : ∀ {W : Type} (K : SimpleGraph W) (f : K ↪g h_subdivided_k33.lineGraph) (i j : W),
      K.Adj i j → (f i : Sym2 (Fin 7)) ≠ f j ∧
        ∃ v, v ∈ (f i : Sym2 (Fin 7)) ∧ v ∈ (f j : Sym2 (Fin 7)) := by
    intro W K f i j h
    have := f.map_rel_iff.2 h
    rw [SimpleGraph.lineGraph_adj_iff_exists] at this
    exact ⟨fun e => this.1 (Subtype.ext e), this.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨f⟩
    have A : ∀ i j : Fin 4, i ≠ j → (f i : Sym2 (Fin 7)) ≠ f j ∧
        ∃ v, v ∈ (f i : Sym2 (Fin 7)) ∧ v ∈ (f j : Sym2 (Fin 7)) :=
      fun i j h => adj _ f i j h
    exact sk33_line_no_four _ sk33_tri sk33_deg _ _ _ _ (f 0).2 (f 1).2 (f 2).2 (f 3).2
      (A 0 1 (by decide)).1 (A 0 2 (by decide)).1 (A 0 3 (by decide)).1 (A 1 2 (by decide)).1
      (A 1 3 (by decide)).1 (A 2 3 (by decide)).1
      (A 0 1 (by decide)).2 (A 0 2 (by decide)).2 (A 1 2 (by decide)).2 (A 1 3 (by decide)).2
      (A 2 3 (by decide)).2
  · rintro ⟨f⟩
    have A : ∀ j : Fin 3, ∃ v, v ∈ (f (Sum.inl 0) : Sym2 (Fin 7)) ∧
        v ∈ (f (Sum.inr j) : Sym2 (Fin 7)) :=
      fun j => (adj _ f (Sum.inl 0) (Sum.inr j) (by simp)).2
    have B : ∀ i j : Fin 3, i ≠ j → ¬ ∃ v, v ∈ (f (Sum.inr i) : Sym2 (Fin 7)) ∧
        v ∈ (f (Sum.inr j) : Sym2 (Fin 7)) := by
      intro i j hij hv
      have hne : f (Sum.inr i) ≠ f (Sum.inr j) := fun e => hij (by simpa using f.injective e)
      have : h_subdivided_k33.lineGraph.Adj (f (Sum.inr i)) (f (Sum.inr j)) := by
        rw [SimpleGraph.lineGraph_adj_iff_exists]
        exact ⟨hne, hv⟩
      rw [f.map_rel_iff] at this
      simp at this
    exact sk33_line_no_claw _ _ _ _ (A 0) (A 1) (A 2) (B 0 1 (by decide)) (B 0 2 (by decide))
      (B 1 2 (by decide))
  · rintro ⟨f⟩
    have A : ∀ i j : Fin 4, diamond_graph.Adj i j → (f i : Sym2 (Fin 7)) ≠ f j ∧
        ∃ v, v ∈ (f i : Sym2 (Fin 7)) ∧ v ∈ (f j : Sym2 (Fin 7)) :=
      fun i j h => adj _ f i j h
    have n03 : (f 0 : Sym2 (Fin 7)) ≠ f 3 := fun e =>
      absurd (f.injective (Subtype.ext e)) (by decide)
    exact sk33_line_no_four _ sk33_tri sk33_deg _ _ _ _ (f 0).2 (f 1).2 (f 2).2 (f 3).2
      (A 0 1 (by simp [diamond_graph])).1 (A 0 2 (by simp [diamond_graph])).1 n03
      (A 1 2 (by simp [diamond_graph])).1
      (A 1 3 (by simp [diamond_graph])).1 (A 2 3 (by simp [diamond_graph])).1
      (A 0 1 (by simp [diamond_graph])).2 (A 0 2 (by simp [diamond_graph])).2
      (A 1 2 (by simp [diamond_graph])).2 (A 1 3 (by simp [diamond_graph])).2
      (A 2 3 (by simp [diamond_graph])).2
