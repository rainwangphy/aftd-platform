import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich
import AFTD.Kb.Tcs.Support

/-!
# op309_small_cyclic_twoport_alternate_two_cut_coloring

Topic: graphs   Node: a398331f6691

Provenance: helper lemma. Explicit alternative-matching witness for the repeated prescribed-matching obstruction in OP-309, experiments 33371 and 33375.

For t at least 2 copies of the displayed two-port graph joined cyclically, use the displayed alternative internal perfect matching. There are a proper four-edge-coloring and matching recoloring with the rich-neighbor property, and both first-bit classes are path forests. Outside the matching, exactly one first-bit-one edge belongs to the long complementary cycle; on the square in each copy, the number of first-bit-one edges is one for copy zero and two in each other copy.
-/

def in1028_int : List (ℕ × ℕ) := [(0,8), (0,9), (1,7), (1,11), (1,13), (2,7), (2,12), (2,13), (3,8), (3,10), (3,11), (4,9), (4,11), (4,12), (5,10), (5,12), (5,13), (6,8), (6,9), (7,10)]
def in1028_look (l : List ((ℕ × ℕ) × ℕ)) (a b : ℕ) : ℕ :=
  (l.lookup (a, b)).getD ((l.lookup (b, a)).getD 0)

/-- base adjacency of the 14-vertex quotient (connector 6-0 included) -/
def in1028_qa (a b : Fin 14) : Prop :=
  ((a.val, b.val) ∈ in1028_int ∨ (b.val, a.val) ∈ in1028_int) ∨
  (a = 6 ∧ b = 0) ∨ (a = 0 ∧ b = 6)

instance (a b : Fin 14) : Decidable (in1028_qa a b) := by unfold in1028_qa; infer_instance

def in1028_nb : Fin 14 → List (Fin 14)
  | 0 => [6, 8, 9] | 1 => [7, 11, 13] | 2 => [7, 12, 13] | 3 => [8, 10, 11]
  | 4 => [9, 11, 12] | 5 => [10, 12, 13] | 6 => [0, 8, 9] | 7 => [1, 2, 10]
  | 8 => [0, 3, 6] | 9 => [0, 4, 6] | 10 => [3, 5, 7] | 11 => [1, 3, 4]
  | 12 => [2, 4, 5] | 13 => [1, 2, 5]

theorem in1028_qa_iff : ∀ a b : Fin 14, in1028_qa a b ↔ b ∈ in1028_nb a := by decide


def in1028_adj {t : ℕ} (x y : ZMod t × Fin 14) : Prop :=
  (x.1 = y.1 ∧ ((x.2.val, y.2.val) ∈ in1028_int ∨ (y.2.val, x.2.val) ∈ in1028_int)) ∨
  (x.2 = 6 ∧ y.2 = 0 ∧ y.1 = x.1 + 1) ∨ (x.2 = 0 ∧ y.2 = 6 ∧ x.1 = y.1 + 1)

theorem in1028_lab {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) {x y : ZMod t × Fin 14} (h : G.Adj x y) :
    y.2 ∈ in1028_nb x.2 := by
  rw [← in1028_qa_iff]
  rcases (hG x y).1 h with ⟨-, h⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem in1028_inj {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) {x y z : ZMod t × Fin 14}
    (hy : G.Adj x y) (hz : G.Adj x z) (hyz : y.2 = z.2) : y = z := by
  rcases (hG x y).1 hy with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rcases (hG x z).1 hz with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
  · exact Prod.ext (h1.symm.trans k1) hyz
  · exfalso; rw [k1, hyz, k2] at h2; exact absurd h2 (by decide)
  · exfalso; rw [k1, hyz, k2] at h2; exact absurd h2 (by decide)
  · exfalso; rw [h1, ← hyz, h2] at k2; exact absurd k2 (by decide)
  · exact Prod.ext (h3.trans k3.symm) hyz
  · exfalso; rw [h1] at k1; exact absurd k1 (by decide)
  · exfalso; rw [h1, ← hyz, h2] at k2; exact absurd k2 (by decide)
  · exfalso; rw [h1] at k1; exact absurd k1 (by decide)
  · exact Prod.ext (add_right_cancel (h3.symm.trans k3)) hyz

theorem in1028_exists_nbr {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) (x : ZMod t × Fin 14) (b : Fin 14)
    (hb : b ∈ in1028_nb x.2) : ∃ y, G.Adj x y ∧ y.2 = b := by
  rw [← in1028_qa_iff] at hb
  rcases hb with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(x.1, b), (hG _ _).2 (Or.inl ⟨rfl, h⟩), rfl⟩
  · exact ⟨(x.1 + 1, b), (hG _ _).2 (Or.inr (Or.inl ⟨h1, h2, rfl⟩)), rfl⟩
  · exact ⟨(x.1 - 1, b), (hG _ _).2 (Or.inr (Or.inr ⟨h1, h2, (sub_add_cancel _ _).symm⟩)), rfl⟩

theorem in1028_same_copy {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) {x y : ZMod t × Fin 14} (h : G.Adj x y)
    (hint : (x.2.val, y.2.val) ∈ in1028_int ∨ (y.2.val, x.2.val) ∈ in1028_int) : x.1 = y.1 := by
  rcases (hG x y).1 h with ⟨h1, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact h1
  · exfalso; rw [h1, h2] at hint; exact absurd hint (by decide)
  · exfalso; rw [h1, h2] at hint; exact absurd hint (by decide)

theorem in1028_line_adj {V : Type*} {G : SimpleGraph V} {e f : G.edgeSet}
    (h : G.lineGraph.Adj e f) :
    ∃ v a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ e.1 = s(v, a) ∧ f.1 = s(v, b) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at h
  obtain ⟨hne, v, hve, hvf⟩ := h
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp hve
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hvf
  have hea : G.Adj v a := by
    have := e.2
    rw [ha, SimpleGraph.mem_edgeSet] at this
    exact this
  have hfb : G.Adj v b := by
    have := f.2
    rw [hb, SimpleGraph.mem_edgeSet] at this
    exact this
  refine ⟨v, a, b, hea, hfb, ?_, ha, hb⟩
  rintro rfl
  exact hne (Subtype.ext (ha.trans hb.symm))

theorem in1028_acyclic_of_rank {W : Type*} (H : SimpleGraph W) (r : W → ℕ)
    (hne : ∀ x y, H.Adj x y → r x ≠ r y)
    (hone : ∀ x y z, H.Adj x y → H.Adj x z → r y < r x → r z < r x → y = z) :
    H.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := c.support.toFinset.exists_max_image r ⟨v, by simp⟩
  rw [List.mem_toFinset] at hm
  have hc' : (c.rotate m hm).IsCycle := hc.rotate hm
  set c' := c.rotate m hm with hc'def
  have hsupp : ∀ x ∈ c'.support, x ∈ c.support := by
    intro x hx
    rw [hc'def, SimpleGraph.Walk.rotate, SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · exact c.support_dropUntil_subset_support hm hx
    · exact c.support_takeUntil_subset_support hm hx
  have hnil : ¬ c'.Nil := hc'.not_nil
  have h1 : H.Adj m c'.snd := c'.adj_snd hnil
  have h2 : H.Adj m c'.penultimate := (c'.adj_penultimate hnil).symm
  have hs1 : c'.snd ∈ c.support := hsupp _ (c'.getVert_mem_support 1)
  have hs2 : c'.penultimate ∈ c.support := hsupp _ (c'.getVert_mem_support _)
  have hr1 := hmax _ (List.mem_toFinset.mpr hs1)
  have hr2 := hmax _ (List.mem_toFinset.mpr hs2)
  have hl1 : r c'.snd < r m := lt_of_le_of_ne hr1 (fun h => hne _ _ h1 h.symm)
  have hl2 : r c'.penultimate < r m := lt_of_le_of_ne hr2 (fun h => hne _ _ h2 h.symm)
  exact hc'.snd_ne_penultimate (hone _ _ _ h1 h2 hl1 hl2)

theorem in1028_side {V : Type*} {G : SimpleGraph V} {f g : G.edgeSet} {x z : V}
    (hf : f.1 = s(x, z)) (h : G.lineGraph.Adj f g) :
    ∃ b, (G.Adj x b ∧ b ≠ z ∧ g.1 = s(x, b)) ∨ (G.Adj z b ∧ b ≠ x ∧ g.1 = s(z, b)) := by
  obtain ⟨v, a, b, ha, hb, hab, he, hg⟩ := in1028_line_adj h
  rw [hf] at he
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2
    exact ⟨b, Or.inl ⟨hb, Ne.symm hab, hg⟩⟩
  · subst h1; subst h2
    exact ⟨b, Or.inr ⟨hb, Ne.symm hab, hg⟩⟩

def in1028_ql : List ((Bool × ℕ × ℕ) × ℕ) := [((true, 0, 8), 2), ((true, 0, 9), 1), ((true, 1, 7), 1), ((true, 1, 11), 0), ((true, 1, 13), 2), ((true, 2, 7), 2), ((true, 2, 12), 0), ((true, 2, 13), 1), ((true, 3, 8), 0), ((true, 3, 10), 1), ((true, 3, 11), 3), ((true, 4, 9), 2), ((true, 4, 11), 1), ((true, 4, 12), 3), ((true, 5, 10), 2), ((true, 5, 12), 1), ((true, 5, 13), 3), ((true, 6, 8), 1), ((true, 6, 9), 3), ((true, 7, 10), 0), ((false, 0, 8), 2), ((false, 0, 9), 1), ((false, 1, 7), 1), ((false, 1, 11), 0), ((false, 1, 13), 3), ((false, 2, 7), 2), ((false, 2, 12), 3), ((false, 2, 13), 1), ((false, 3, 8), 0), ((false, 3, 10), 1), ((false, 3, 11), 2), ((false, 4, 9), 0), ((false, 4, 11), 1), ((false, 4, 12), 2), ((false, 5, 10), 3), ((false, 5, 12), 1), ((false, 5, 13), 2), ((false, 6, 8), 1), ((false, 6, 9), 3), ((false, 7, 10), 0)]
def in1028_dl : List ((Bool × ℕ × Bool × ℕ) × ℕ) := [((true, 0, true, 8), 0), ((true, 0, true, 9), 0), ((true, 1, true, 7), 0), ((true, 1, true, 11), 1), ((true, 1, true, 13), 0), ((true, 2, true, 7), 0), ((true, 2, true, 12), 0), ((true, 2, true, 13), 1), ((true, 3, true, 8), 3), ((true, 3, true, 10), 2), ((true, 3, true, 11), 0), ((true, 4, true, 9), 0), ((true, 4, true, 11), 2), ((true, 4, true, 12), 1), ((true, 5, true, 10), 2), ((true, 5, true, 12), 1), ((true, 5, true, 13), 1), ((true, 6, true, 8), 4), ((true, 6, true, 9), 1), ((true, 7, true, 10), 1), ((false, 0, false, 8), 0), ((false, 0, false, 9), 0), ((false, 1, false, 7), 4), ((false, 1, false, 11), 3), ((false, 1, false, 13), 0), ((false, 2, false, 7), 0), ((false, 2, false, 12), 1), ((false, 2, false, 13), 0), ((false, 3, false, 8), 7), ((false, 3, false, 10), 6), ((false, 3, false, 11), 0), ((false, 4, false, 9), 1), ((false, 4, false, 11), 2), ((false, 4, false, 12), 2), ((false, 5, false, 10), 2), ((false, 5, false, 12), 0), ((false, 5, false, 13), 1), ((false, 6, false, 8), 8), ((false, 6, false, 9), 0), ((false, 7, false, 10), 5), ((true, 6, false, 0), 5), ((false, 6, true, 0), 9), ((false, 6, false, 0), 9)]

abbrev in1028_Ty := Bool × Fin 14
def in1028_conn (a c : Fin 14) : Bool := (a == 6 && c == 0) || (a == 0 && c == 6)
def in1028_qI (b : Bool) (a c : ℕ) : ℕ :=
  (in1028_ql.lookup (b, a, c)).getD ((in1028_ql.lookup (b, c, a)).getD 0)
def in1028_qT (v w : in1028_Ty) : Fin 4 :=
  if in1028_conn v.2 w.2 then 0 else ⟨in1028_qI (v.1 && w.1) v.2.val w.2.val % 4, Nat.mod_lt _ (by decide)⟩
def in1028_dT (v w : in1028_Ty) : ℕ :=
  (in1028_dl.lookup (v.1, v.2.val, w.1, w.2.val)).getD ((in1028_dl.lookup (w.1, w.2.val, v.1, v.2.val)).getD 0)
def in1028_ml : List (ℕ × ℕ) := [(0,9), (1,7), (3,8), (5,12)]
def in1028_mB (a c : Fin 14) : Bool := decide ((a.val, c.val) ∈ in1028_ml ∨ (c.val, a.val) ∈ in1028_ml)
def in1028_cT (v w : in1028_Ty) : Fin 5 :=
  if in1028_mB v.2 w.2 then 4 else ⟨(in1028_qT v w).val, Nat.lt_trans (in1028_qT v w).isLt (by decide)⟩
def in1028_inb : Fin 14 → List (Fin 14)
  | 0 => [8, 9] | 1 => [7, 11, 13] | 2 => [7, 12, 13] | 3 => [8, 10, 11]
  | 4 => [9, 11, 12] | 5 => [10, 12, 13] | 6 => [8, 9] | 7 => [1, 2, 10]
  | 8 => [0, 3, 6] | 9 => [0, 4, 6] | 10 => [3, 5, 7] | 11 => [1, 3, 4]
  | 12 => [2, 4, 5] | 13 => [1, 2, 5]
def in1028_tnb (v : in1028_Ty) : List in1028_Ty :=
  (in1028_inb v.2).map (fun a => (v.1, a)) ++
  (if v.2 = 6 then (if v.1 then [(false, 0)] else [(true, 0), (false, 0)])
   else if v.2 = 0 then (if v.1 then [(false, 6)] else [(true, 6), (false, 6)]) else [])
def in1028_hi (v w : in1028_Ty) : Prop := 2 ≤ (in1028_qT v w).val
instance (v w : in1028_Ty) : Decidable (in1028_hi v w) := by unfold in1028_hi; infer_instance
def in1028_endp (a c : Fin 14) : Bool := (a == 0 && c == 9) || (a == 9 && c == 0)
def in1028_lowB (V A B : in1028_Ty) : Bool :=
  if V.2 = 0 ∧ A.2 = 6 then false else if V.2 = 0 ∧ B.2 = 6 then true
  else decide (in1028_dT V B < in1028_dT V A)
def in1028_fixp (u v : Fin 14) : Prop :=
  (u.val, v.val) ∈ ([(0,8), (1,13), (2,7), (3,11), (4,12), (5,10), (6,9)] : List (ℕ × ℕ)) ∨
  (v.val, u.val) ∈ ([(0,8), (1,13), (2,7), (3,11), (4,12), (5,10), (6,9)] : List (ℕ × ℕ))
instance (u v : Fin 14) : Decidable (in1028_fixp u v) := by unfold in1028_fixp; infer_instance
def in1028_intp (u v : Fin 14) : Prop :=
  (u.val, v.val) ∈ in1028_int ∨ (v.val, u.val) ∈ in1028_int
instance (u v : Fin 14) : Decidable (in1028_intp u v) := by unfold in1028_intp; infer_instance

def in1028_richB (V W : in1028_Ty) : Prop :=
  (∀ O ∈ in1028_tnb V, ∀ O' ∈ in1028_tnb V, O.2 ≠ W.2 → O'.2 ≠ W.2 → O.2 ≠ O'.2 →
    in1028_cT V O ≠ in1028_cT V O') ∧
  (∀ O ∈ in1028_tnb W, ∀ O' ∈ in1028_tnb W, O.2 ≠ V.2 → O'.2 ≠ V.2 → O.2 ≠ O'.2 →
    in1028_cT W O ≠ in1028_cT W O') ∧
  (∀ O ∈ in1028_tnb V, ∀ O' ∈ in1028_tnb W, O.2 ≠ W.2 → O'.2 ≠ V.2 → in1028_cT V O ≠ in1028_cT W O')
set_option synthInstance.maxSize 2000 in
instance (V W : in1028_Ty) : Decidable (in1028_richB V W) := by unfold in1028_richB; infer_instance

theorem in1028_qT_symm : ∀ v w : in1028_Ty, in1028_qT v w = in1028_qT w v := by decide
theorem in1028_dT_symm : ∀ v w : in1028_Ty, in1028_dT v w = in1028_dT w v := by decide
theorem in1028_mB_symm : ∀ a c : Fin 14, in1028_mB a c = in1028_mB c a := by decide
theorem in1028_endp_symm : ∀ a c : Fin 14, in1028_endp a c = in1028_endp c a := by decide
theorem in1028_cT_symm (v w : in1028_Ty) : in1028_cT v w = in1028_cT w v := by
  simp only [in1028_cT, in1028_mB_symm v.2 w.2, in1028_qT_symm v w]
theorem in1028_dT_lt : ∀ v w : in1028_Ty, in1028_dT v w < 32 := by decide
theorem in1028_bf1 : ∀ (b : Bool) (a c : Fin 14), in1028_intp a c → (b, c) ∈ in1028_tnb (b, a) := by
  decide
theorem in1028_bf2 : ∀ b b' : Bool, ¬ (b = true ∧ b' = true) →
    (b', (0 : Fin 14)) ∈ in1028_tnb (b, 6) ∧ (b', (6 : Fin 14)) ∈ in1028_tnb (b, 0) := by decide
theorem in1028_conn_not_int : ∀ a c : Fin 14, in1028_intp a c → in1028_conn a c = false := by decide
theorem in1028_base_proper : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V, A.2 ≠ B.2 →
    in1028_qT V A ≠ in1028_qT V B := by decide
theorem in1028_base_cproper : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V, A.2 ≠ B.2 →
    in1028_cT V A ≠ in1028_cT V B := by decide
theorem in1028_base_match : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V, A.2 ≠ B.2 →
    ¬ (in1028_mB V.2 A.2 = true ∧ in1028_mB V.2 B.2 = true) := by decide
set_option maxRecDepth 4000 in
set_option synthInstance.maxSize 4000 in
theorem in1028_base_rich : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V,
    (∃ o ∈ in1028_nb V.2, o ≠ A.2 ∧ ∀ Z ∈ in1028_tnb V, Z.2 = o → in1028_richB V Z) ∨
    (∃ o ∈ in1028_nb A.2, o ≠ V.2 ∧ ∀ Z ∈ in1028_tnb A, Z.2 = o → in1028_richB A Z) := by decide
theorem in1028_base_fix : ∀ (b : Bool) (u v : Fin 14), in1028_fixp u v → 2 ≤ (in1028_qT (b, u) (b, v)).val := by
  decide
theorem in1028_base_fix_int : ∀ u v : Fin 14, in1028_fixp u v → in1028_intp u v := by decide

def in1028_sqp (u : Fin 14) : Prop := u = 2 ∨ u = 5 ∨ u = 12 ∨ u = 13
instance (u : Fin 14) : Decidable (in1028_sqp u) := by unfold in1028_sqp; infer_instance

theorem in1028_base_high : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, 2 ≤ (in1028_qT V A).val →
    in1028_fixp V.2 A.2 ∨ (in1028_sqp V.2 ∧ in1028_sqp A.2 ∧ in1028_intp V.2 A.2) ∨
    (V = (true, 4) ∧ A = (true, 9)) ∨ (V = (true, 9) ∧ A = (true, 4)) := by decide
theorem in1028_base_square : ∀ (b : Bool) (u v : Fin 14), in1028_intp u v → in1028_sqp u → in1028_sqp v →
    2 ≤ (in1028_qT (b, u) (b, v)).val →
    ((u = 5 ∧ v = 13) ∨ (u = 13 ∧ v = 5)) ∨ (b = false ∧ ((u = 2 ∧ v = 12) ∨ (u = 12 ∧ v = 2))) := by
  decide
theorem in1028_base_R1 : ∀ V : in1028_Ty, V.1 = true → ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V,
    in1028_conn V.2 A.2 = false → in1028_conn V.2 B.2 = false → A.2 ≠ B.2 →
    (in1028_hi V A ↔ in1028_hi V B) → in1028_endp V.2 A.2 = in1028_endp V.2 B.2 := by decide
theorem in1028_base_R2 : ∀ V : in1028_Ty, V.1 = true → V.2 = 0 → ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V,
    A.2 = 6 → B.2 ≠ 6 → (in1028_hi V A ↔ in1028_hi V B) → B.2 = 9 := by decide
theorem in1028_base_R3 : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V, A.2 ≠ B.2 →
    (in1028_hi V A ↔ in1028_hi V B) → in1028_lowB V A B = true ∨ in1028_lowB V B A = true := by decide
theorem in1028_base_rone1 : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V, ∀ B' ∈ in1028_tnb V,
    A.2 ≠ B.2 → A.2 ≠ B'.2 → B.2 ≠ B'.2 → (in1028_hi V A ↔ in1028_hi V B) →
    (in1028_hi V A ↔ in1028_hi V B') → in1028_lowB V A B = true → in1028_lowB V A B' = true → False := by
  decide
theorem in1028_base_rone2 : ∀ V : in1028_Ty, ∀ A ∈ in1028_tnb V, ∀ B ∈ in1028_tnb V, ∀ B' ∈ in1028_tnb A,
    B.2 ≠ A.2 → B'.2 ≠ V.2 → (in1028_hi V A ↔ in1028_hi V B) → (in1028_hi A V ↔ in1028_hi A B') →
    in1028_lowB V A B = true → in1028_lowB A V B' = true → False := by decide

def in1028_tau {t : ℕ} (x : ZMod t × Fin 14) : in1028_Ty := (decide (x.1 = 0), x.2)

theorem in1028_tlab {t : ℕ} (ht : 2 ≤ t) {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) {x y : ZMod t × Fin 14} (h : G.Adj x y) :
    in1028_tau y ∈ in1028_tnb (in1028_tau x) := by
  have : Fact (1 < t) := ⟨by omega⟩
  have key : ∀ i j : ZMod t, (j = i + 1 ∨ i = j + 1) → ¬ (decide (i = 0) = true ∧ decide (j = 0) = true) := by
    rintro i j hij ⟨hi, hj⟩
    rw [decide_eq_true_eq] at hi hj
    subst hi; subst hj
    rcases hij with h | h <;> simp at h
  rcases (hG x y).1 h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · unfold in1028_tau
    rw [← h1]
    exact in1028_bf1 _ _ _ h2
  · unfold in1028_tau
    rw [h1, h2]
    exact (in1028_bf2 _ _ (key _ _ (Or.inl h3))).1
  · unfold in1028_tau
    rw [h1, h2]
    exact (in1028_bf2 _ _ (key _ _ (Or.inr h3))).2

def in1028_levE {t : ℕ} (x y : ZMod t × Fin 14) : ℕ :=
  if x.2 = 6 ∧ y.2 = 0 then x.1.val else if x.2 = 0 ∧ y.2 = 6 then y.1.val
  else if x.1 = 0 ∧ y.1 = 0 ∧ in1028_endp x.2 y.2 = true then t else min x.1.val y.1.val

def in1028_levV {t : ℕ} (v a : ZMod t × Fin 14) : ℕ :=
  if v.2 = 6 ∧ a.2 = 0 then v.1.val else if v.2 = 0 ∧ a.2 = 6 then a.1.val
  else if v.1 = 0 ∧ in1028_endp v.2 a.2 = true then t else v.1.val

theorem in1028_levAt {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) {v a : ZMod t × Fin 14} (h : G.Adj v a) :
    in1028_levE v a + in1028_levE a v = 2 * in1028_levV v a := by
  rcases (hG v a).1 h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hc := in1028_conn_not_int _ _ h2
    have n1 : ¬ (v.2 = 6 ∧ a.2 = 0) := by
      rintro ⟨e1, e2⟩; rw [e1, e2] at hc; exact absurd hc (by decide)
    have n2 : ¬ (v.2 = 0 ∧ a.2 = 6) := by
      rintro ⟨e1, e2⟩; rw [e1, e2] at hc; exact absurd hc (by decide)
    have n1' : ¬ (a.2 = 6 ∧ v.2 = 0) := fun h => n2 ⟨h.2, h.1⟩
    have n2' : ¬ (a.2 = 0 ∧ v.2 = 6) := fun h => n1 ⟨h.2, h.1⟩
    have he := in1028_endp_symm v.2 a.2
    unfold in1028_levE in1028_levV
    rw [if_neg n1, if_neg n2, if_neg n1', if_neg n2', if_neg n1, if_neg n2, ← h1, he]
    split_ifs <;> first | omega | simp_all | (exfalso; simp_all)
  · unfold in1028_levE in1028_levV
    have n : ¬ (a.2 = 6 ∧ v.2 = 0) := by rintro ⟨e, -⟩; rw [h2] at e; exact absurd e (by decide)
    rw [if_pos ⟨h1, h2⟩, if_neg n, if_pos ⟨h2, h1⟩, if_pos ⟨h1, h2⟩]; ring
  · unfold in1028_levE in1028_levV
    have n : ¬ (v.2 = 6 ∧ a.2 = 0) := by rintro ⟨e, -⟩; rw [h1] at e; exact absurd e (by decide)
    rw [if_neg n, if_pos ⟨h1, h2⟩, if_pos ⟨h2, h1⟩, if_neg n, if_pos ⟨h1, h2⟩]; ring

theorem in1028_val_succ {t : ℕ} [NeZero t] (ht : 2 ≤ t) (i : ZMod t) :
    (i + 1 ≠ 0 → (i + 1).val = i.val + 1) ∧ (i + 1 = 0 → i.val + 1 = t) := by
  haveI : Fact (1 < t) := ⟨by omega⟩
  have hv : (i + 1).val = (i.val + 1) % t := by rw [ZMod.val_add, ZMod.val_one]
  have hlt := ZMod.val_lt i
  constructor
  · intro h
    rw [hv]
    apply Nat.mod_eq_of_lt
    rcases Nat.lt_or_ge (i.val + 1) t with h' | h'
    · exact h'
    · exfalso; apply h
      rw [← ZMod.val_eq_zero, hv, show i.val + 1 = t by omega, Nat.mod_self]
  · intro h
    have h0 : (i + 1).val = 0 := by rw [h, ZMod.val_zero]
    rw [hv] at h0
    rcases Nat.lt_or_ge (i.val + 1) t with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h0; omega
    · omega

def in1028_qL {t : ℕ} : Sym2 (ZMod t × Fin 14) → Fin 4 :=
  Sym2.lift ⟨fun x y => in1028_qT (in1028_tau x) (in1028_tau y), fun _ _ => in1028_qT_symm _ _⟩
def in1028_cL {t : ℕ} : Sym2 (ZMod t × Fin 14) → Fin 5 :=
  Sym2.lift ⟨fun x y => in1028_cT (in1028_tau x) (in1028_tau y), fun _ _ => in1028_cT_symm _ _⟩
def in1028_mL {t : ℕ} : Sym2 (ZMod t × Fin 14) → Bool :=
  Sym2.lift ⟨fun x y => in1028_mB x.2 y.2, fun _ _ => in1028_mB_symm _ _⟩
def in1028_rL {t : ℕ} : Sym2 (ZMod t × Fin 14) → ℕ :=
  Sym2.lift ⟨fun x y => 32 * (in1028_levE x y + in1028_levE y x) +
    in1028_dT (in1028_tau x) (in1028_tau y), fun x y => by dsimp only; rw [add_comm (in1028_levE x y), in1028_dT_symm]⟩

theorem in1028_conn_false {a c : Fin 14} (h1 : ¬ (a = 6 ∧ c = 0)) (h2 : ¬ (a = 0 ∧ c = 6)) :
    in1028_conn a c = false := by
  cases h : in1028_conn a c
  · rfl
  · exfalso
    unfold in1028_conn at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact h1 h
    · exact h2 h

theorem in1028_rank_cmp {t : ℕ} [NeZero t] (ht : 2 ≤ t) {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) {v a b : ZMod t × Fin 14}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a.2 ≠ b.2)
    (hcl : in1028_hi (in1028_tau v) (in1028_tau a) ↔ in1028_hi (in1028_tau v) (in1028_tau b)) :
    in1028_rL s(v, b) < in1028_rL s(v, a) ↔
      in1028_lowB (in1028_tau v) (in1028_tau a) (in1028_tau b) = true := by
  have e1 : in1028_rL s(v, a) = 64 * in1028_levV v a + in1028_dT (in1028_tau v) (in1028_tau a) := by
    show 32 * (in1028_levE v a + in1028_levE a v) + _ = _
    rw [in1028_levAt hG ha]; ring
  have e2 : in1028_rL s(v, b) = 64 * in1028_levV v b + in1028_dT (in1028_tau v) (in1028_tau b) := by
    show 32 * (in1028_levE v b + in1028_levE b v) + _ = _
    rw [in1028_levAt hG hb]; ring
  rw [e1, e2]
  have d1 := in1028_dT_lt (in1028_tau v) (in1028_tau a)
  have d2 := in1028_dT_lt (in1028_tau v) (in1028_tau b)
  have ta := in1028_tlab ht hG ha
  have tb := in1028_tlab ht hG hb
  -- incoming connectors force the copy relation
  have hin : ∀ {w : ZMod t × Fin 14}, G.Adj v w → v.2 = 0 → w.2 = 6 → v.1 = w.1 + 1 := by
    intro w hw h0 h6
    rcases (hG v w).1 hw with ⟨_, h2⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
    · exfalso; have := in1028_conn_not_int _ _ h2; rw [h0, h6] at this; exact absurd this (by decide)
    · exfalso; rw [h0] at h1; exact absurd h1 (by decide)
    · exact h3
  -- level of an internal edge at an incoming-connector vertex
  have hstep : ∀ {w z : ZMod t × Fin 14}, G.Adj v w → G.Adj v z → v.2 = 0 → w.2 = 6 → z.2 ≠ 6 →
      (in1028_hi (in1028_tau v) (in1028_tau w) ↔ in1028_hi (in1028_tau v) (in1028_tau z)) →
      in1028_levV v z = in1028_levV v w + 1 := by
    intro w z hw hz h0 h6 hz6 hc
    have hvw := hin hw h0 h6
    unfold in1028_levV
    have nz1 : ¬ (v.2 = 6 ∧ z.2 = 0) := fun h => by rw [h0] at h; exact absurd h.1 (by decide)
    have nz2 : ¬ (v.2 = 0 ∧ z.2 = 6) := fun h => hz6 h.2
    have nw1 : ¬ (v.2 = 6 ∧ w.2 = 0) := fun h => by rw [h0] at h; exact absurd h.1 (by decide)
    rw [if_neg nz1, if_neg nz2, if_neg nw1, if_pos (show v.2 = 0 ∧ w.2 = 6 from ⟨h0, h6⟩)]
    have hs := in1028_val_succ ht w.1
    by_cases hv0 : v.1 = 0
    · have hz9 := in1028_base_R2 (in1028_tau v) (by simp [in1028_tau, hv0]) h0 (in1028_tau w)
        (in1028_tlab ht hG hw) (in1028_tau z) (in1028_tlab ht hG hz) h6 hz6 hc
      have he : in1028_endp v.2 z.2 = true := by
        rw [h0, show z.2 = 9 from hz9]; decide
      rw [if_pos (show v.1 = 0 ∧ in1028_endp v.2 z.2 = true from ⟨hv0, he⟩)]
      exact (hs.2 (by rw [← hvw]; exact hv0)).symm
    · have hn : ¬ (v.1 = 0 ∧ in1028_endp v.2 z.2 = true) := fun h => hv0 h.1
      rw [if_neg hn, hvw]
      exact hs.1 (by rw [← hvw]; exact hv0)
  unfold in1028_lowB
  change _ ↔ (if v.2 = 0 ∧ a.2 = 6 then false else if v.2 = 0 ∧ b.2 = 6 then true
    else decide (in1028_dT (in1028_tau v) (in1028_tau b) < in1028_dT (in1028_tau v) (in1028_tau a))) = true
  by_cases hA : v.2 = 0 ∧ a.2 = 6
  · rw [if_pos hA]
    have hb6 : b.2 ≠ 6 := fun h => hab (hA.2.trans h.symm)
    have hl := hstep ha hb hA.1 hA.2 hb6 hcl
    rw [hl]
    simp only [Bool.false_eq_true, iff_false, not_lt]
    omega
  · rw [if_neg hA]
    by_cases hB : v.2 = 0 ∧ b.2 = 6
    · rw [if_pos hB]
      have ha6 : a.2 ≠ 6 := fun h => hab (h.trans hB.2.symm)
      have hl := hstep hb ha hB.1 hB.2 ha6 hcl.symm
      rw [hl]
      simp only [iff_true]
      omega
    · rw [if_neg hB]
      have hlev : in1028_levV v a = in1028_levV v b := by
        unfold in1028_levV
        rw [if_neg hA, if_neg hB]
        by_cases hA' : v.2 = 6 ∧ a.2 = 0
        · have hB' : ¬ (v.2 = 6 ∧ b.2 = 0) := fun h => hab (hA'.2.trans h.2.symm)
          have he : ¬ (v.1 = 0 ∧ in1028_endp v.2 b.2 = true) := by
            rintro ⟨-, h⟩; rw [hA'.1] at h; revert h; generalize b.2 = c; revert c; decide
          rw [if_pos hA', if_neg hB', if_neg he]
        · by_cases hB' : v.2 = 6 ∧ b.2 = 0
          · have he : ¬ (v.1 = 0 ∧ in1028_endp v.2 a.2 = true) := by
              rintro ⟨-, h⟩; rw [hB'.1] at h; revert h; generalize a.2 = c; revert c; decide
            rw [if_neg hA', if_pos hB', if_neg he]
          · rw [if_neg hA', if_neg hB']
            by_cases hv0 : v.1 = 0
            · have hR := in1028_base_R1 (in1028_tau v) (by simp [in1028_tau, hv0]) (in1028_tau a) ta
                (in1028_tau b) tb (in1028_conn_false hA' hA) (in1028_conn_false hB' hB) hab hcl
              change in1028_endp v.2 a.2 = in1028_endp v.2 b.2 at hR
              rw [hR]
            · have h1 : ¬ (v.1 = 0 ∧ in1028_endp v.2 a.2 = true) := fun h => hv0 h.1
              have h2 : ¬ (v.1 = 0 ∧ in1028_endp v.2 b.2 = true) := fun h => hv0 h.1
              rw [if_neg h1, if_neg h2]
      rw [hlev, decide_eq_true_iff]
      omega

theorem in1028_rich_at {t : ℕ} (ht : 2 ≤ t) {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1028_adj x y) (c : G.lineGraph.Coloring (Fin 5))
    (hc : ∀ f : G.edgeSet, c f = in1028_cL f.1) {x y z : ZMod t × Fin 14}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z)
    (hr : in1028_richB (in1028_tau x) (in1028_tau z)) :
    G.lineGraph.Adj ⟨s(x, y), hxy⟩ ⟨s(x, z), hxz⟩ ∧
      simple_graph_edge_is_rich G c ⟨s(x, z), hxz⟩ := by
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hyz ?_, x, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    have h' := congrArg Subtype.val h
    simp only [Sym2.eq_iff] at h'
    rcases h' with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (G.ne_of_adj hxz)
  · intro g h hg hh hgh
    have hne : ∀ {p q r : ZMod t × Fin 14}, G.Adj p q → G.Adj p r → q ≠ r → q.2 ≠ r.2 :=
      fun hq hr hqr h => hqr (in1028_inj hG hq hr h)
    have hzx : G.Adj z x := hxz.symm
    obtain ⟨b, hb⟩ := in1028_side (f := ⟨s(x, z), hxz⟩) rfl hg
    obtain ⟨b', hb'⟩ := in1028_side (f := ⟨s(x, z), hxz⟩) rfl hh
    rw [hc g, hc h]
    rcases hb with ⟨hxb, hbz, hgb⟩ | ⟨hzb, hbx, hgb⟩ <;>
      rcases hb' with ⟨hxb', hbz', hhb'⟩ | ⟨hzb', hbx', hhb'⟩ <;> rw [hgb, hhb']
    · have hbb : b ≠ b' := by
        rintro rfl
        exact hgh (Subtype.ext (hgb.trans hhb'.symm))
      exact hr.1 _ (in1028_tlab ht hG hxb) _ (in1028_tlab ht hG hxb') (hne hxb hxz hbz)
        (hne hxb' hxz hbz') (hne hxb hxb' hbb)
    · exact hr.2.2 _ (in1028_tlab ht hG hxb) _ (in1028_tlab ht hG hzb') (hne hxb hxz hbz)
        (hne hzb' hzx hbx')
    · exact (hr.2.2 _ (in1028_tlab ht hG hxb') _ (in1028_tlab ht hG hzb) (hne hxb' hxz hbz')
        (hne hzb hzx hbx)).symm
    · have hbb : b ≠ b' := by
        rintro rfl
        exact hgh (Subtype.ext (hgb.trans hhb'.symm))
      exact hr.2.1 _ (in1028_tlab ht hG hzb) _ (in1028_tlab ht hG hzb') (hne hzb hzx hbx)
        (hne hzb' hzx hbx') (hne hzb hzb' hbb)

theorem in1028_sq_of_mem : ∀ u : Fin 14, u ∈ ({2, 5, 12, 13} : Finset (Fin 14)) → in1028_sqp u := by
  decide
theorem in1028_mem_of_sq : ∀ u : Fin 14, in1028_sqp u → u ∈ ({2, 5, 12, 13} : Finset (Fin 14)) := by
  decide
theorem in1028_hi513 : ∀ b : Bool, 2 ≤ (in1028_qT (b, 5) (b, 13)).val := by decide
theorem in1028_hi212 : 2 ≤ (in1028_qT (false, 2) (false, 12)).val := by decide
theorem in1028_hi49 : 2 ≤ (in1028_qT (true, 4) (true, 9)).val := by decide

theorem in1028_sym2_pair {t : ℕ} {x y : ZMod t × Fin 14} {i : ZMod t} {u v : Fin 14}
    (h1 : x = (i, u)) (h2 : y = (i, v)) : s(x, y) = s((i, u), (i, v)) := by rw [h1, h2]

theorem in1028_labels_of_eq {t : ℕ} {i j : ZMod t} {a b u v : Fin 14}
    (h : s((i, a), (i, b)) = s((j, u), (j, v))) : (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Prod.mk.injEq] at h1 h2
    exact Or.inl ⟨h1.2.symm, h2.2.symm⟩
  · rw [Prod.mk.injEq] at h1 h2
    exact Or.inr ⟨h2.2.symm, h1.2.symm⟩

theorem op309_small_cyclic_twoport_alternate_two_cut_coloring
    (t : ℕ) [NeZero t] (ht : 2 ≤ t)
    (G : SimpleGraph (ZMod t × Fin 14)) [DecidableRel G.Adj]
    (hG : ∀ x y : ZMod t × Fin 14, G.Adj x y ↔
      (x.1 = y.1 ∧
        ((x.2.val,y.2.val) ∈ ([(0,8), (0,9), (1,7), (1,11), (1,13), (2,7), (2,12), (2,13), (3,8), (3,10), (3,11), (4,9), (4,11), (4,12), (5,10), (5,12), (5,13), (6,8), (6,9), (7,10)] : List (ℕ × ℕ)) ∨
         (y.2.val,x.2.val) ∈ ([(0,8), (0,9), (1,7), (1,11), (1,13), (2,7), (2,12), (2,13), (3,8), (3,10), (3,11), (4,9), (4,11), (4,12), (5,10), (5,12), (5,13), (6,8), (6,9), (7,10)] : List (ℕ × ℕ)))) ∨
      (x.2 = 6 ∧ y.2 = 0 ∧ y.1 = x.1 + 1) ∨
      (x.2 = 0 ∧ y.2 = 6 ∧ x.1 = y.1 + 1)) :
    let fixed : G.edgeSet → Prop := fun f =>
      ∃ (i : ZMod t) (u v : Fin 14),
        ((u.val,v.val) ∈ ([(0,8), (1,13), (2,7), (3,11), (4,12), (5,10), (6,9)] : List (ℕ × ℕ)) ∨
         (v.val,u.val) ∈ ([(0,8), (1,13), (2,7), (3,11), (4,12), (5,10), (6,9)] : List (ℕ × ℕ))) ∧ f.1 = s((i,u),(i,v))
    let square : ZMod t → G.edgeSet → Prop := fun i f =>
      ∃ u v : Fin 14, u ∈ ({2,5,12,13} : Finset (Fin 14)) ∧
        v ∈ ({2,5,12,13} : Finset (Fin 14)) ∧ f.1 = s((i,u),(i,v))
    ∃ (q : G.lineGraph.Coloring (Fin 4)) (M : Finset G.edgeSet)
      (c : G.lineGraph.Coloring (Fin 5)),
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ G.lineGraph.Adj e f) ∧
      (∀ f : G.edgeSet, c f =
        if f ∈ M then 4 else ⟨(q f).val, Nat.lt_trans (q f).isLt (by decide)⟩) ∧
      simple_graph_is_rich_neighbor_coloring G c ∧
      (∀ f : G.edgeSet, fixed f → 2 ≤ (q f).val) ∧
      ((Finset.univ : Finset G.edgeSet).filter fun f =>
        2 ≤ (q f).val ∧ ¬ fixed f ∧ ¬ ∃ i : ZMod t, square i f).card = 1 ∧
      (∀ i : ZMod t, ((Finset.univ : Finset G.edgeSet).filter fun f =>
        2 ≤ (q f).val ∧ square i f).card = if i = 0 then 1 else 2) ∧
      ∃ H : SimpleGraph G.edgeSet, H.IsAcyclic ∧
        ∀ e f : G.edgeSet, H.Adj e f ↔ G.lineGraph.Adj e f ∧
          ((2 ≤ (q e).val) ↔ (2 ≤ (q f).val)) := by
  classical
  intro fixed square
  have hG' : ∀ x y, G.Adj x y ↔ in1028_adj x y := hG
  have hne : ∀ {p q r : ZMod t × Fin 14}, G.Adj p q → G.Adj p r → q ≠ r → q.2 ≠ r.2 :=
    fun hq hr hqr h => hqr (in1028_inj hG' hq hr h)
  have tl : ∀ {x y : ZMod t × Fin 14}, G.Adj x y → in1028_tau y ∈ in1028_tnb (in1028_tau x) :=
    fun h => in1028_tlab ht hG' h
  let q : G.lineGraph.Coloring (Fin 4) := SimpleGraph.Coloring.mk (fun f => in1028_qL f.1) (by
    intro e f h
    obtain ⟨v, a, b, ha, hb, hab, he, hf⟩ := in1028_line_adj h
    show in1028_qL e.1 ≠ in1028_qL f.1
    rw [he, hf]
    exact in1028_base_proper _ _ (tl ha) _ (tl hb) (hne ha hb hab))
  have hq : ∀ f : G.edgeSet, q f = in1028_qL f.1 := fun f => rfl
  let M : Finset G.edgeSet := Finset.univ.filter (fun f => in1028_mL f.1 = true)
  let c : G.lineGraph.Coloring (Fin 5) := SimpleGraph.Coloring.mk (fun f => in1028_cL f.1) (by
    intro e f h
    obtain ⟨v, a, b, ha, hb, hab, he, hf⟩ := in1028_line_adj h
    show in1028_cL e.1 ≠ in1028_cL f.1
    rw [he, hf]
    exact in1028_base_cproper _ _ (tl ha) _ (tl hb) (hne ha hb hab))
  have hc : ∀ f : G.edgeSet, c f = in1028_cL f.1 := fun f => rfl
  -- edges of copy i with given labels
  have hadjI : ∀ (i : ZMod t) (u v : Fin 14), in1028_intp u v → G.Adj (i, u) (i, v) :=
    fun i u v h => (hG' _ _).2 (Or.inl ⟨rfl, h⟩)
  refine ⟨q, M, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- M is a matching
    intro e he f hf hef hadj
    obtain ⟨v, a, b, ha, hb, hab, he', hf'⟩ := in1028_line_adj hadj
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
    rw [he'] at he
    rw [hf'] at hf
    exact in1028_base_match _ _ (tl ha) _ (tl hb) (hne ha hb hab) ⟨he, hf⟩
  · -- c is the recolouring
    intro f
    rw [hc, hq]
    rcases f with ⟨z, hz⟩
    induction z using Sym2.ind with
    | h x y =>
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
      show in1028_cT (in1028_tau x) (in1028_tau y) = if in1028_mB x.2 y.2 = true then 4 else _
      unfold in1028_cT
      dsimp only [in1028_tau]
      by_cases h1 : in1028_mB x.2 y.2 = true
      · simp only [h1, if_true]
      · simp only [h1, if_false]
        rfl
  · -- rich neighbours
    intro e _
    rcases e with ⟨w, hw⟩
    induction w using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := hw
      rcases in1028_base_rich (in1028_tau x) (in1028_tau y) (tl hxy) with
        ⟨o, ho, hoy, hall⟩ | ⟨o, ho, hox, hall⟩
      · obtain ⟨z, hxz, hz2⟩ := in1028_exists_nbr hG' x o ho
        have hr := hall (in1028_tau z) (tl hxz) hz2
        have hyz : y ≠ z := fun h => hoy (by rw [← hz2, h]; rfl)
        obtain ⟨hadj, hrich⟩ := in1028_rich_at ht hG' c hc hxy hxz hyz hr
        exact ⟨_, hadj, hrich⟩
      · obtain ⟨z, hyz', hz2⟩ := in1028_exists_nbr hG' y o ho
        have hr := hall (in1028_tau z) (tl hyz') hz2
        have hxz : x ≠ z := fun h => hox (by rw [← hz2, h]; rfl)
        obtain ⟨hadj, hrich⟩ := in1028_rich_at ht hG' c hc hxy.symm hyz' hxz hr
        have heq : (⟨s(x, y), hw⟩ : G.edgeSet) = ⟨s(y, x), hxy.symm⟩ := Subtype.ext Sym2.eq_swap
        rw [heq]
        exact ⟨_, hadj, hrich⟩
  · -- fixed edges are high
    rintro f ⟨i, u, v, huv, hf⟩
    rw [hq, hf]
    exact in1028_base_fix (decide (i = 0)) u v huv
  · -- exactly one further high non-square edge
    let estar : G.edgeSet := ⟨s((0, 4), (0, 9)), hadjI 0 4 9 (by decide)⟩
    rw [Finset.card_eq_one]
    refine ⟨estar, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hhi, hnf, hns⟩
      rcases f with ⟨w, hw⟩
      induction w using Sym2.ind with
      | h x y =>
        have hxy : G.Adj x y := hw
        rw [hq] at hhi
        change 2 ≤ (in1028_qT (in1028_tau x) (in1028_tau y)).val at hhi
        rcases in1028_base_high _ _ (tl hxy) hhi with hfix | ⟨hs1, hs2, hint⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso
          apply hnf
          have hcopy := in1028_same_copy hG' hxy (in1028_base_fix_int _ _ hfix)
          exact ⟨x.1, x.2, y.2, hfix, in1028_sym2_pair rfl (Prod.ext hcopy.symm rfl)⟩
        · exfalso
          apply hns
          have hcopy := in1028_same_copy hG' hxy hint
          exact ⟨x.1, x.2, y.2, in1028_mem_of_sq _ hs1, in1028_mem_of_sq _ hs2,
            in1028_sym2_pair rfl (Prod.ext hcopy.symm rfl)⟩
        · simp only [in1028_tau, Prod.mk.injEq, decide_eq_true_eq] at h1 h2
          exact Subtype.ext (in1028_sym2_pair (Prod.ext h1.1 h1.2) (Prod.ext h2.1 h2.2))
        · simp only [in1028_tau, Prod.mk.injEq, decide_eq_true_eq] at h1 h2
          apply Subtype.ext
          show s(x, y) = s((0, 4), (0, 9))
          rw [Sym2.eq_swap]
          exact in1028_sym2_pair (Prod.ext h2.1 h2.2) (Prod.ext h1.1 h1.2)
    · rintro rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hq]
        show 2 ≤ (in1028_qT (in1028_tau ((0 : ZMod t), (4 : Fin 14))) (in1028_tau ((0 : ZMod t), (9 : Fin 14)))).val
        simp only [in1028_tau, decide_true]
        exact in1028_hi49
      · rintro ⟨i, u, v, huv, hf⟩
        rcases in1028_labels_of_eq hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at huv <;>
          exact absurd huv (by decide)
      · rintro ⟨i, u, v, hu, hv, hf⟩
        rcases in1028_labels_of_eq hf with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at hu <;>
          exact absurd hu (by decide)
  · -- square counts
    intro i
    let s513 : G.edgeSet := ⟨s((i, 5), (i, 13)), hadjI i 5 13 (by decide)⟩
    let s212 : G.edgeSet := ⟨s((i, 2), (i, 12)), hadjI i 2 12 (by decide)⟩
    have hmem : ∀ f : G.edgeSet, (2 ≤ (q f).val ∧ square i f) ↔
        (f = s513 ∨ (i ≠ 0 ∧ f = s212)) := by
      intro f
      constructor
      · rintro ⟨hhi, u, v, hu, hv, hf⟩
        have hadj : G.Adj (i, u) (i, v) := by
          have := f.2
          rw [hf] at this
          exact this
        have hint : in1028_intp u v := by
          rcases (hG' _ _).1 hadj with ⟨-, h⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
          · exact h
          · exfalso; rw [show u = 6 from h1] at hu; exact absurd hu (by decide)
          · exfalso; rw [show u = 0 from h1] at hu; exact absurd hu (by decide)
        rw [hq, hf] at hhi
        change 2 ≤ (in1028_qT (decide (i = 0), u) (decide (i = 0), v)).val at hhi
        rcases in1028_base_square _ u v hint (in1028_sq_of_mem _ hu) (in1028_sq_of_mem _ hv) hhi with
          (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨hb, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
        · left; apply Subtype.ext; rw [hf, h1, h2]
        · left; apply Subtype.ext; rw [hf, h1, h2]; exact Sym2.eq_swap
        · right
          refine ⟨fun h => by simp [h] at hb, ?_⟩
          apply Subtype.ext; rw [hf, h1, h2]
        · right
          refine ⟨fun h => by simp [h] at hb, ?_⟩
          apply Subtype.ext; rw [hf, h1, h2]; exact Sym2.eq_swap
      · rintro (rfl | ⟨hi0, rfl⟩)
        · refine ⟨?_, 5, 13, by decide, by decide, rfl⟩
          rw [hq]
          exact in1028_hi513 _
        · refine ⟨?_, 2, 12, by decide, by decide, rfl⟩
          rw [hq]
          show 2 ≤ (in1028_qT (decide (i = 0), 2) (decide (i = 0), 12)).val
          rw [decide_eq_false hi0]
          exact in1028_hi212
    have hne2 : s513 ≠ s212 := by
      intro h
      have h' := congrArg Subtype.val h
      rcases in1028_labels_of_eq h' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by decide)
    by_cases hi0 : i = 0
    · rw [if_pos hi0, Finset.card_eq_one]
      refine ⟨s513, ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hmem]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact h
        · exact absurd hi0 h
      · intro h; exact Or.inl h
    · rw [if_neg hi0, Finset.card_eq_two]
      refine ⟨s513, s212, hne2, ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, hmem]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨hi0, h⟩
  · -- the equal-class graph is acyclic
    let H : SimpleGraph G.edgeSet :=
      { Adj := fun e f => G.lineGraph.Adj e f ∧ ((2 ≤ (q e).val) ↔ (2 ≤ (q f).val))
        symm := ⟨fun e f h => ⟨h.1.symm, h.2.symm⟩⟩
        loopless := ⟨fun e h => h.1.ne rfl⟩ }
    refine ⟨H, ?_, fun e f => Iff.rfl⟩
    apply in1028_acyclic_of_rank H (fun f => in1028_rL f.1)
    · intro e f h
      obtain ⟨v, a, b, ha, hb, hab, he, hf⟩ := in1028_line_adj h.1
      have hcl : in1028_hi (in1028_tau v) (in1028_tau a) ↔ in1028_hi (in1028_tau v) (in1028_tau b) := by
        have := h.2
        rw [hq, hq, he, hf] at this
        exact this
      show in1028_rL e.1 ≠ in1028_rL f.1
      rw [he, hf]
      rcases in1028_base_R3 _ _ (tl ha) _ (tl hb) (hne ha hb hab) hcl with h1 | h1
      · exact ((in1028_rank_cmp ht hG' ha hb (hne ha hb hab) hcl).2 h1).ne'
      · exact ((in1028_rank_cmp ht hG' hb ha (hne hb ha (Ne.symm hab)) hcl.symm).2 h1).ne
    · intro x y z hxy hxz hy hz
      obtain ⟨v, a, b, ha, hb, hab, hx1, hy1⟩ := in1028_line_adj hxy.1
      obtain ⟨v', a', b', ha', hb', hab', hx2, hz1⟩ := in1028_line_adj hxz.1
      have hc1 : in1028_hi (in1028_tau v) (in1028_tau a) ↔ in1028_hi (in1028_tau v) (in1028_tau b) := by
        have := hxy.2
        rw [hq, hq, hx1, hy1] at this
        exact this
      have hy' : in1028_rL s(v, b) < in1028_rL s(v, a) := by
        rw [← hx1, ← hy1]; exact hy
      have low1 := (in1028_rank_cmp ht hG' ha hb (hne ha hb hab) hc1).1 hy'
      have hx12 : s(v, a) = s(v', a') := hx1.symm.trans hx2
      rcases Sym2.eq_iff.1 hx12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        have hc2 : in1028_hi (in1028_tau v) (in1028_tau a) ↔ in1028_hi (in1028_tau v) (in1028_tau b') := by
          have := hxz.2
          rw [hq, hq, hx1, hz1] at this
          exact this
        have hz' : in1028_rL s(v, b') < in1028_rL s(v, a) := by
          rw [← hx1, ← hz1]; exact hz
        have low2 := (in1028_rank_cmp ht hG' ha hb' (hne ha hb' hab') hc2).1 hz'
        by_cases hbb : b.2 = b'.2
        · have := in1028_inj hG' hb hb' hbb
          subst this
          exact Subtype.ext (hy1.trans hz1.symm)
        · exact (in1028_base_rone1 _ _ (tl ha) _ (tl hb) _ (tl hb') (hne ha hb hab)
            (hne ha hb' hab') hbb hc1 hc2 low1 low2).elim
      · subst h1; subst h2
        have hxs : x.1 = s(a, v) := hx1.trans Sym2.eq_swap
        have hc2 : in1028_hi (in1028_tau a) (in1028_tau v) ↔ in1028_hi (in1028_tau a) (in1028_tau b') := by
          have := hxz.2
          rw [hq, hq, hxs, hz1] at this
          exact this
        have hz' : in1028_rL s(a, b') < in1028_rL s(a, v) := by
          rw [← hxs, ← hz1]; exact hz
        have low2 := (in1028_rank_cmp ht hG' ha' hb' (hne ha' hb' hab') hc2).1 hz'
        exact (in1028_base_rone2 _ _ (tl ha) _ (tl hb) _ (tl hb') (hne ha hb hab).symm
          (hne ha' hb' hab').symm hc1 hc2 low1 low2).elim
