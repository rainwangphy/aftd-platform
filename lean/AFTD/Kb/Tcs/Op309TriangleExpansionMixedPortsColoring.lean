import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_triangle_expansion_mixed_ports_coloring

Topic: graphs   Node: a701ac6c64b3

Provenance: helper lemma. Explicit construction for the triangle expansion partial case of OP-309, tested in experiments 31379 and 31384.

A finite graph formed from disjoint triangles by pairing vertices across triangles has a rich-neighbor five-edge-coloring whenever its paired ports carry equal Boolean labels and each triangle has both labels.
-/

theorem op309_tex_adj_cases {V : Type*} (G : SimpleGraph V) (e f : G.edgeSet) (p q : V)
    (he : (e : Sym2 V) = s(p, q)) (hadj : G.lineGraph.Adj e f) :
    ∃ t, (G.Adj p t ∧ t ≠ q ∧ (f : Sym2 V) = s(p, t)) ∨
         (G.Adj q t ∧ t ≠ p ∧ (f : Sym2 V) = s(q, t)) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, y, hye, hyf⟩ := hadj
  rw [he, Sym2.mem_iff] at hye
  obtain ⟨t, ht⟩ := Sym2.mem_iff_exists.mp hyf
  have hft : G.Adj y t := by
    have := f.2; rw [ht] at this; exact (SimpleGraph.mem_edgeSet G).mp this
  refine ⟨t, ?_⟩
  rcases hye with rfl | rfl
  · left
    refine ⟨hft, ?_, ht⟩
    rintro rfl; exact hne (Subtype.ext (he.trans ht.symm))
  · right
    refine ⟨hft, ?_, ht⟩
    rintro rfl; exact hne (Subtype.ext (he.trans (ht.trans Sym2.eq_swap).symm))

def op309_tex_tc (i j : Fin 3) : Fin 5 := ![![0, 4, 3], ![4, 0, 2], ![3, 2, 0]] i j

theorem op309_tex_tc_symm : ∀ i j : Fin 3, op309_tex_tc i j = op309_tex_tc j i := by decide

theorem op309_tex_tri_ne_tri : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    op309_tex_tc i j ≠ op309_tex_tc i k := by decide

theorem op309_tex_tri_ne_bool : ∀ i j : Fin 3, i ≠ j → ∀ bb : Bool,
    op309_tex_tc i j ≠ (if bb then 1 else 0) := by decide

theorem op309_tex_tri_ne_tri2 : ∀ i j j1 j2 : Fin 3, i ≠ j → j1 ≠ i → j1 ≠ j → j2 ≠ j → j2 ≠ i →
    op309_tex_tc i j1 ≠ op309_tex_tc j j2 := by decide

theorem op309_tex_third : ∀ a b : Fin 3, ∃ k : Fin 3, k ≠ a ∧ k ≠ b := by decide

theorem op309_tex_bool_ne : ∀ a b : Bool, a ≠ b → (if a then (1 : Fin 5) else 0) ≠ (if b then 1 else 0) := by decide

theorem op309_triangle_expansion_mixed_ports_coloring
    {B : Type*} [Fintype B] [DecidableEq B]
    (p : B × Fin 3 → B × Fin 3) (hp : Function.Involutive p)
    (hcross : ∀ v, (p v).1 ≠ v.1)
    (P : B × Fin 3 → Bool) (hP : ∀ v, P v = P (p v))
    (hmixed : ∀ b : B, (∃ i : Fin 3, P (b,i) = true) ∧
                       (∃ j : Fin 3, P (b,j) = false))
    (G : SimpleGraph (B × Fin 3)) [DecidableRel G.Adj]
    (hG : ∀ u v, G.Adj u v ↔
      (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ v = p u) :
    ∃ c : G.lineGraph.Coloring (Fin 5), simple_graph_is_rich_neighbor_coloring G c := by
  classical
  let col : B × Fin 3 → B × Fin 3 → Fin 5 := fun x y =>
    if x.1 = y.1 then op309_tex_tc x.2 y.2 else (if (P x && P y) then 1 else 0)
  have hcolsymm : ∀ x y, col x y = col y x := by
    intro x y
    simp only [col, eq_comm (a := x.1), op309_tex_tc_symm x.2 y.2, Bool.and_comm]
  let f : Sym2 (B × Fin 3) → Fin 5 := Sym2.lift ⟨col, hcolsymm⟩
  have hf : ∀ x y, f s(x, y) = col x y := fun x y => rfl
  -- colours at a vertex
  have hcross_col : ∀ w, col w (p w) = if P w then 1 else 0 := by
    intro w
    simp only [col, if_neg (Ne.symm (hcross w)), ← hP w, Bool.and_self]
  have hL : ∀ w x y, G.Adj w x → G.Adj w y → x ≠ y → col w x ≠ col w y := by
    intro w x y hx hy hxy
    rcases (hG w x).mp hx with ⟨h1, h2⟩ | h1 <;> rcases (hG w y).mp hy with ⟨h3, h4⟩ | h3
    · have hxy2 : x.2 ≠ y.2 := by
        intro h
        exact hxy (Prod.ext (h1.symm.trans h3) h)
      simp only [col, if_pos h1, if_pos h3]
      exact op309_tex_tri_ne_tri w.2 x.2 y.2 h2 h4 hxy2
    · subst h3
      rw [hcross_col]
      simp only [col, if_pos h1]
      exact op309_tex_tri_ne_bool w.2 x.2 h2 (P w)
    · subst h1
      rw [hcross_col]
      simp only [col, if_pos h3]
      exact (op309_tex_tri_ne_bool w.2 y.2 h4 (P w)).symm
    · exact absurd (h1.trans h3.symm) hxy
  -- the colouring
  have hproper : ∀ {e e' : G.edgeSet}, G.lineGraph.Adj e e' → f e.1 ≠ f e'.1 := by
    intro e e' hadj
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ q : (B × Fin 3) × (B × Fin 3), (e : Sym2 _) = s(q.1, q.2) := by
      induction (e : Sym2 (B × Fin 3)) using Sym2.ind with
      | h a b => exact ⟨(a, b), rfl⟩
    have hGxy : G.Adj x y := by have := e.2; rw [hxy] at this; exact this
    obtain ⟨t, ⟨ht, hty, hft⟩ | ⟨ht, htx, hft⟩⟩ := op309_tex_adj_cases G e e' x y hxy hadj
    · rw [hxy, hft, hf, hf]
      exact (hL x y t hGxy ht (Ne.symm hty))
    · rw [hxy, hft, hf, hf, hcolsymm x y]
      exact (hL y x t hGxy.symm ht (Ne.symm htx))
  let c : G.lineGraph.Coloring (Fin 5) := SimpleGraph.Coloring.mk (fun e => f e.1) hproper
  have hc : ∀ e : G.edgeSet, c e = f e.1 := fun e => rfl
  -- mixed triangle edges are rich
  have hrich : ∀ (e : G.edgeSet) (w x : B × Fin 3), (e : Sym2 _) = s(w, x) → w.1 = x.1 → w.2 ≠ x.2 →
      P w ≠ P x → simple_graph_edge_is_rich G c e := by
    intro e w x he hwx1 hwx2 hPwx
    intro g1 g2 hg1 hg2 hne hcol
    rw [hc, hc] at hcol
    obtain ⟨t1, ⟨ht1, ht1x, hg1e⟩ | ⟨ht1, ht1w, hg1e⟩⟩ := op309_tex_adj_cases G e g1 w x he hg1 <;>
    obtain ⟨t2, ⟨ht2, ht2x, hg2e⟩ | ⟨ht2, ht2w, hg2e⟩⟩ := op309_tex_adj_cases G e g2 w x he hg2 <;>
    rw [hg1e, hg2e, hf, hf] at hcol
    · by_cases h12 : t1 = t2
      · exact hne (Subtype.ext (by rw [hg1e, hg2e, h12]))
      · exact hL w t1 t2 ht1 ht2 h12 hcol
    · -- g1 at w, g2 at x
      rcases (hG w t1).mp ht1 with ⟨a1, a2⟩ | a1 <;> rcases (hG x t2).mp ht2 with ⟨b1, b2⟩ | b1
      · simp only [col, if_pos a1, if_pos b1] at hcol
        have ht1w2 : t1.2 ≠ x.2 := fun h => ht1x (Prod.ext (a1.symm.trans hwx1) h)
        have ht2w2 : t2.2 ≠ w.2 := fun h => ht2w (Prod.ext (b1.symm.trans hwx1.symm) h)
        exact op309_tex_tri_ne_tri2 w.2 x.2 t1.2 t2.2 hwx2 (Ne.symm a2) ht1w2 (Ne.symm b2) ht2w2 hcol
      · subst b1
        rw [hcross_col] at hcol
        simp only [col, if_pos a1] at hcol
        exact op309_tex_tri_ne_bool w.2 t1.2 a2 (P x) hcol
      · subst a1
        rw [hcross_col] at hcol
        simp only [col, if_pos b1] at hcol
        exact op309_tex_tri_ne_bool x.2 t2.2 b2 (P w) hcol.symm
      · subst a1; subst b1
        rw [hcross_col, hcross_col] at hcol
        exact op309_tex_bool_ne _ _ hPwx hcol
    · -- g1 at x, g2 at w
      rcases (hG x t1).mp ht1 with ⟨a1, a2⟩ | a1 <;> rcases (hG w t2).mp ht2 with ⟨b1, b2⟩ | b1
      · simp only [col, if_pos a1, if_pos b1] at hcol
        have ht1w2 : t1.2 ≠ w.2 := fun h => ht1w (Prod.ext (a1.symm.trans hwx1.symm) h)
        have ht2x2 : t2.2 ≠ x.2 := fun h => ht2x (Prod.ext (b1.symm.trans hwx1) h)
        exact op309_tex_tri_ne_tri2 w.2 x.2 t2.2 t1.2 hwx2 (Ne.symm b2) ht2x2 (Ne.symm a2) ht1w2 hcol.symm
      · subst b1
        rw [hcross_col] at hcol
        simp only [col, if_pos a1] at hcol
        exact op309_tex_tri_ne_bool x.2 t1.2 a2 (P w) hcol
      · subst a1
        rw [hcross_col] at hcol
        simp only [col, if_pos b1] at hcol
        exact op309_tex_tri_ne_bool w.2 t2.2 b2 (P x) hcol.symm
      · subst a1; subst b1
        rw [hcross_col, hcross_col] at hcol
        exact op309_tex_bool_ne _ _ hPwx hcol.symm
    · by_cases h12 : t1 = t2
      · exact hne (Subtype.ext (by rw [hg1e, hg2e, h12]))
      · exact hL x t1 t2 ht1 ht2 h12 hcol
  -- every edge meets a rich edge
  have hadjG : ∀ (b : B) (i j : Fin 3), i ≠ j → G.Adj (b, i) (b, j) :=
    fun b i j h => (hG _ _).mpr (Or.inl ⟨rfl, h⟩)
  refine ⟨c, ?_⟩
  intro e _
  obtain ⟨⟨x, y⟩, hxy⟩ : ∃ q : (B × Fin 3) × (B × Fin 3), (e : Sym2 _) = s(q.1, q.2) := by
    induction (e : Sym2 (B × Fin 3)) using Sym2.ind with
    | h a b => exact ⟨(a, b), rfl⟩
  obtain ⟨b, ix⟩ := x
  have hq : ∃ q : Fin 3, P (b, q) ≠ P (b, ix) := by
    obtain ⟨⟨i1, hi1⟩, ⟨i0, hi0⟩⟩ := hmixed b
    cases hx : P (b, ix)
    · exact ⟨i1, by rw [hi1]; decide⟩
    · exact ⟨i0, by rw [hi0]; decide⟩
  obtain ⟨q, hqP⟩ := hq
  have hqix : q ≠ ix := fun h => hqP (by rw [h])
  let r : G.edgeSet := ⟨s((b, ix), (b, q)), hadjG b ix q (Ne.symm hqix)⟩
  have hr : simple_graph_edge_is_rich G c r :=
    hrich r (b, ix) (b, q) rfl rfl (Ne.symm hqix) (Ne.symm hqP)
  by_cases her : e = r
  · -- e is itself the rich edge; use the third vertex
    obtain ⟨k, hkix, hkq⟩ := op309_tex_third ix q
    by_cases hPk : P (b, k) = P (b, ix)
    · let r2 : G.edgeSet := ⟨s((b, k), (b, q)), hadjG b k q hkq⟩
      refine ⟨r2, ?_, hrich r2 (b, k) (b, q) rfl rfl hkq (by rw [hPk]; exact Ne.symm hqP)⟩
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨fun h => ?_, (b, q), by rw [her]; simp [r], by simp [r2]⟩
      have hm : (b, k) ∈ (e : Sym2 (B × Fin 3)) := by rw [h]; simp [r2]
      rw [her] at hm
      simp [r] at hm
      rcases hm with h' | h'
      · exact hkix h'
      · exact hkq h'
    · let r2 : G.edgeSet := ⟨s((b, ix), (b, k)), hadjG b ix k (Ne.symm hkix)⟩
      refine ⟨r2, ?_, hrich r2 (b, ix) (b, k) rfl rfl (Ne.symm hkix) (Ne.symm hPk)⟩
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨fun h => ?_, (b, ix), by rw [her]; simp [r], by simp [r2]⟩
      have hm : (b, k) ∈ (e : Sym2 (B × Fin 3)) := by rw [h]; simp [r2]
      rw [her] at hm
      simp [r] at hm
      rcases hm with h' | h'
      · exact hkix h'
      · exact hkq h'
  · refine ⟨r, ?_, hr⟩
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨her, (b, ix), by rw [hxy]; simp, by simp [r]⟩
