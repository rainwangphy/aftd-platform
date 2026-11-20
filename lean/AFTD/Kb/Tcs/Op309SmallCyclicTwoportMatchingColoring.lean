import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich
import AFTD.Kb.Tcs.Support

/-!
# op309_small_cyclic_twoport_matching_coloring

Topic: graphs   Node: cd433be6f900

Provenance: helper lemma. Explicit periodic witnesses for the repeated prescribed-matching cut obstruction, experiment 33343.

For t at least 2, the cyclically joined gadget graph has a proper four-edge-coloring and matching recoloring with the rich-neighbor property, whose first-bit-one class contains the displayed matching plus exactly t further edges and whose equal-first-bit edge adjacency graph is acyclic.
-/

def in1025_int : List (ℕ × ℕ) := [(0,8), (0,9), (1,7), (1,11), (1,13), (2,7), (2,12), (2,13), (3,8), (3,10), (3,11), (4,9), (4,11), (4,12), (5,10), (5,12), (5,13), (6,8), (6,9), (7,10)]
def in1025_fix : List (ℕ × ℕ) := [(0,8), (1,7), (2,12), (3,10), (4,11), (5,13), (6,9)]
def in1025_ql : List ((ℕ × ℕ) × ℕ) := [((0, 8), 3), ((0, 9), 0), ((1, 7), 2), ((1, 11), 1), ((1, 13), 0), ((2, 7), 0), ((2, 12), 2), ((2, 13), 3), ((3, 8), 1), ((3, 10), 2), ((3, 11), 0), ((4, 9), 1), ((4, 11), 3), ((4, 12), 0), ((5, 10), 0), ((5, 12), 1), ((5, 13), 2), ((6, 8), 0), ((6, 9), 2), ((7, 10), 1), ((6, 0), 1)]
def in1025_rl : List ((ℕ × ℕ) × ℕ) := [((0, 8), 0), ((0, 9), 0), ((1, 7), 0), ((1, 11), 5), ((1, 13), 6), ((2, 7), 6), ((2, 12), 0), ((2, 13), 1), ((3, 8), 3), ((3, 10), 0), ((3, 11), 4), ((4, 9), 1), ((4, 11), 0), ((4, 12), 2), ((5, 10), 4), ((5, 12), 3), ((5, 13), 2), ((6, 8), 2), ((6, 9), 0), ((7, 10), 5), ((6, 0), 1)]
def in1025_ml : List (ℕ × ℕ) := [(1, 7), (3, 11), (4, 12), (5, 10), (6, 0)]

def in1025_look (l : List ((ℕ × ℕ) × ℕ)) (a b : ℕ) : ℕ :=
  (l.lookup (a, b)).getD ((l.lookup (b, a)).getD 0)

/-- base adjacency of the 14-vertex quotient (connector 6-0 included) -/
def in1025_qa (a b : Fin 14) : Prop :=
  ((a.val, b.val) ∈ in1025_int ∨ (b.val, a.val) ∈ in1025_int) ∨
  (a = 6 ∧ b = 0) ∨ (a = 0 ∧ b = 6)

instance (a b : Fin 14) : Decidable (in1025_qa a b) := by unfold in1025_qa; infer_instance

def in1025_nb : Fin 14 → List (Fin 14)
  | 0 => [6, 8, 9] | 1 => [7, 11, 13] | 2 => [7, 12, 13] | 3 => [8, 10, 11]
  | 4 => [9, 11, 12] | 5 => [10, 12, 13] | 6 => [0, 8, 9] | 7 => [1, 2, 10]
  | 8 => [0, 3, 6] | 9 => [0, 4, 6] | 10 => [3, 5, 7] | 11 => [1, 3, 4]
  | 12 => [2, 4, 5] | 13 => [1, 2, 5]

theorem in1025_qa_iff : ∀ a b : Fin 14, in1025_qa a b ↔ b ∈ in1025_nb a := by decide

def in1025_qF (a b : Fin 14) : Fin 4 := ⟨in1025_look in1025_ql a.val b.val % 4, Nat.mod_lt _ (by decide)⟩
def in1025_mB (a b : Fin 14) : Bool := decide ((a.val, b.val) ∈ in1025_ml ∨ (b.val, a.val) ∈ in1025_ml)
def in1025_cF (a b : Fin 14) : Fin 5 :=
  if in1025_mB a b then 4 else ⟨(in1025_qF a b).val, Nat.lt_trans (in1025_qF a b).isLt (by decide)⟩
def in1025_rF (a b : Fin 14) : ℕ := in1025_look in1025_rl a.val b.val
def in1025_hi (a b : Fin 14) : Prop := 2 ≤ (in1025_qF a b).val

theorem in1025_qF_symm : ∀ a b : Fin 14, in1025_qF a b = in1025_qF b a := by decide
theorem in1025_mB_symm : ∀ a b : Fin 14, in1025_mB a b = in1025_mB b a := by decide
theorem in1025_rF_symm : ∀ a b : Fin 14, in1025_rF a b = in1025_rF b a := by decide

-- base checks
theorem in1025_base_proper : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, ∀ b ∈ in1025_nb v, a ≠ b →
    in1025_qF v a ≠ in1025_qF v b := by decide
theorem in1025_base_match : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, ∀ b ∈ in1025_nb v, a ≠ b →
    ¬ (in1025_mB v a = true ∧ in1025_mB v b = true) := by decide

def in1025_adj {t : ℕ} (x y : ZMod t × Fin 14) : Prop :=
  (x.1 = y.1 ∧ ((x.2.val, y.2.val) ∈ in1025_int ∨ (y.2.val, x.2.val) ∈ in1025_int)) ∨
  (x.2 = 6 ∧ y.2 = 0 ∧ y.1 = x.1 + 1) ∨ (x.2 = 0 ∧ y.2 = 6 ∧ x.1 = y.1 + 1)

theorem in1025_lab {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1025_adj x y) {x y : ZMod t × Fin 14} (h : G.Adj x y) :
    y.2 ∈ in1025_nb x.2 := by
  rw [← in1025_qa_iff]
  rcases (hG x y).1 h with ⟨-, h⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem in1025_inj {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1025_adj x y) {x y z : ZMod t × Fin 14}
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

theorem in1025_exists_nbr {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1025_adj x y) (x : ZMod t × Fin 14) (b : Fin 14)
    (hb : b ∈ in1025_nb x.2) : ∃ y, G.Adj x y ∧ y.2 = b := by
  rw [← in1025_qa_iff] at hb
  rcases hb with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(x.1, b), (hG _ _).2 (Or.inl ⟨rfl, h⟩), rfl⟩
  · exact ⟨(x.1 + 1, b), (hG _ _).2 (Or.inr (Or.inl ⟨h1, h2, rfl⟩)), rfl⟩
  · exact ⟨(x.1 - 1, b), (hG _ _).2 (Or.inr (Or.inr ⟨h1, h2, (sub_add_cancel _ _).symm⟩)), rfl⟩

theorem in1025_same_copy {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1025_adj x y) {x y : ZMod t × Fin 14} (h : G.Adj x y)
    (hint : (x.2.val, y.2.val) ∈ in1025_int ∨ (y.2.val, x.2.val) ∈ in1025_int) : x.1 = y.1 := by
  rcases (hG x y).1 h with ⟨h1, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact h1
  · exfalso; rw [h1, h2] at hint; exact absurd hint (by decide)
  · exfalso; rw [h1, h2] at hint; exact absurd hint (by decide)

theorem in1025_line_adj {V : Type*} {G : SimpleGraph V} {e f : G.edgeSet}
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

theorem in1025_acyclic_of_rank {W : Type*} (H : SimpleGraph W) (r : W → ℕ)
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

def in1025_richB (a b : Fin 14) : Prop :=
  (∀ o ∈ in1025_nb a, ∀ o' ∈ in1025_nb a, o ≠ b → o' ≠ b → o ≠ o' → in1025_cF a o ≠ in1025_cF a o') ∧
  (∀ o ∈ in1025_nb b, ∀ o' ∈ in1025_nb b, o ≠ a → o' ≠ a → o ≠ o' → in1025_cF b o ≠ in1025_cF b o') ∧
  (∀ o ∈ in1025_nb a, ∀ o' ∈ in1025_nb b, o ≠ b → o' ≠ a → in1025_cF a o ≠ in1025_cF b o')

set_option synthInstance.maxSize 2000 in
instance (a b : Fin 14) : Decidable (in1025_richB a b) := by unfold in1025_richB; infer_instance

theorem in1025_base_rich : ∀ a : Fin 14, ∀ b ∈ in1025_nb a,
    (∃ o ∈ in1025_nb a, o ≠ b ∧ in1025_richB a o) ∨ (∃ o ∈ in1025_nb b, o ≠ a ∧ in1025_richB b o) := by
  decide
theorem in1025_base_cproper : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, ∀ b ∈ in1025_nb v, a ≠ b →
    in1025_cF v a ≠ in1025_cF v b := by decide
theorem in1025_base_ne : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, v ≠ a := by decide
theorem in1025_base_fix : ∀ u v : Fin 14,
    ((u.val, v.val) ∈ in1025_fix ∨ (v.val, u.val) ∈ in1025_fix) → 2 ≤ (in1025_qF u v).val := by decide
theorem in1025_base_fix_int : ∀ u v : Fin 14,
    ((u.val, v.val) ∈ in1025_fix ∨ (v.val, u.val) ∈ in1025_fix) →
    ((u.val, v.val) ∈ in1025_int ∨ (v.val, u.val) ∈ in1025_int) := by decide
theorem in1025_base_high : ∀ a : Fin 14, ∀ b ∈ in1025_nb a, 2 ≤ (in1025_qF a b).val →
    ((a.val, b.val) ∈ in1025_fix ∨ (b.val, a.val) ∈ in1025_fix) ∨ (a = 2 ∧ b = 13) ∨ (a = 13 ∧ b = 2) := by
  decide
theorem in1025_base_rne : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, ∀ b ∈ in1025_nb v, a ≠ b →
    (in1025_hi v a ↔ in1025_hi v b) → in1025_rF v a ≠ in1025_rF v b := by
  unfold in1025_hi; decide
theorem in1025_base_rone1 : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, ∀ b ∈ in1025_nb v, ∀ b' ∈ in1025_nb v,
    a ≠ b → a ≠ b' → b ≠ b' → (in1025_hi v a ↔ in1025_hi v b) → (in1025_hi v a ↔ in1025_hi v b') →
    in1025_rF v b < in1025_rF v a → in1025_rF v b' < in1025_rF v a → False := by
  unfold in1025_hi; decide
theorem in1025_base_rone2 : ∀ v : Fin 14, ∀ a ∈ in1025_nb v, ∀ b ∈ in1025_nb v, ∀ b' ∈ in1025_nb a,
    b ≠ a → b' ≠ v → (in1025_hi v a ↔ in1025_hi v b) → (in1025_hi v a ↔ in1025_hi a b') →
    in1025_rF v b < in1025_rF v a → in1025_rF a b' < in1025_rF v a → False := by
  unfold in1025_hi; decide

def in1025_qL {t : ℕ} : Sym2 (ZMod t × Fin 14) → Fin 4 :=
  Sym2.lift ⟨fun x y => in1025_qF x.2 y.2, fun _ _ => in1025_qF_symm _ _⟩
def in1025_mL {t : ℕ} : Sym2 (ZMod t × Fin 14) → Bool :=
  Sym2.lift ⟨fun x y => in1025_mB x.2 y.2, fun _ _ => in1025_mB_symm _ _⟩
def in1025_rL {t : ℕ} : Sym2 (ZMod t × Fin 14) → ℕ :=
  Sym2.lift ⟨fun x y => in1025_rF x.2 y.2, fun _ _ => in1025_rF_symm _ _⟩
theorem in1025_cF_symm (a b : Fin 14) : in1025_cF a b = in1025_cF b a := by
  simp only [in1025_cF, in1025_mB_symm a b, in1025_qF_symm a b]
def in1025_cL {t : ℕ} : Sym2 (ZMod t × Fin 14) → Fin 5 :=
  Sym2.lift ⟨fun x y => in1025_cF x.2 y.2, fun _ _ => in1025_cF_symm _ _⟩

theorem in1025_side {V : Type*} {G : SimpleGraph V} {f g : G.edgeSet} {x z : V}
    (hf : f.1 = s(x, z)) (h : G.lineGraph.Adj f g) :
    ∃ b, (G.Adj x b ∧ b ≠ z ∧ g.1 = s(x, b)) ∨ (G.Adj z b ∧ b ≠ x ∧ g.1 = s(z, b)) := by
  obtain ⟨v, a, b, ha, hb, hab, he, hg⟩ := in1025_line_adj h
  rw [hf] at he
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2
    exact ⟨b, Or.inl ⟨hb, Ne.symm hab, hg⟩⟩
  · subst h1; subst h2
    exact ⟨b, Or.inr ⟨hb, Ne.symm hab, hg⟩⟩

theorem in1025_rich_at {t : ℕ} {G : SimpleGraph (ZMod t × Fin 14)}
    (hG : ∀ x y, G.Adj x y ↔ in1025_adj x y) (c : G.lineGraph.Coloring (Fin 5))
    (hc : ∀ f : G.edgeSet, c f = in1025_cL f.1) {x y z : ZMod t × Fin 14}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) (hr : in1025_richB x.2 z.2) :
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
      fun hq hr hqr h => hqr (in1025_inj hG hq hr h)
    have hzx : G.Adj z x := hxz.symm
    obtain ⟨b, hb⟩ := in1025_side (f := ⟨s(x, z), hxz⟩) rfl hg
    obtain ⟨b', hb'⟩ := in1025_side (f := ⟨s(x, z), hxz⟩) rfl hh
    rw [hc g, hc h]
    rcases hb with ⟨hxb, hbz, hgb⟩ | ⟨hzb, hbx, hgb⟩ <;>
      rcases hb' with ⟨hxb', hbz', hhb'⟩ | ⟨hzb', hbx', hhb'⟩ <;> rw [hgb, hhb']
    · have hbb : b ≠ b' := by
        rintro rfl
        exact hgh (Subtype.ext (hgb.trans hhb'.symm))
      exact hr.1 _ (in1025_lab hG hxb) _ (in1025_lab hG hxb') (hne hxb hxz hbz)
        (hne hxb' hxz hbz') (hne hxb hxb' hbb)
    · exact hr.2.2 _ (in1025_lab hG hxb) _ (in1025_lab hG hzb') (hne hxb hxz hbz)
        (hne hzb' hzx hbx')
    · exact (hr.2.2 _ (in1025_lab hG hxb') _ (in1025_lab hG hzb) (hne hxb' hxz hbz')
        (hne hzb hzx hbx)).symm
    · have hbb : b ≠ b' := by
        rintro rfl
        exact hgh (Subtype.ext (hgb.trans hhb'.symm))
      exact hr.2.1 _ (in1025_lab hG hzb) _ (in1025_lab hG hzb') (hne hzb hzx hbx)
        (hne hzb' hzx hbx') (hne hzb hzb' hbb)

theorem op309_small_cyclic_twoport_matching_coloring
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
        ((u.val,v.val) ∈ ([(0,8), (1,7), (2,12), (3,10), (4,11), (5,13), (6,9)] : List (ℕ × ℕ)) ∨
         (v.val,u.val) ∈ ([(0,8), (1,7), (2,12), (3,10), (4,11), (5,13), (6,9)] : List (ℕ × ℕ))) ∧ f.1 = s((i,u),(i,v))
    ∃ (q : G.lineGraph.Coloring (Fin 4)) (M : Finset G.edgeSet)
      (c : G.lineGraph.Coloring (Fin 5)),
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ G.lineGraph.Adj e f) ∧
      (∀ f : G.edgeSet, c f =
        if f ∈ M then 4 else ⟨(q f).val, Nat.lt_trans (q f).isLt (by decide)⟩) ∧
      simple_graph_is_rich_neighbor_coloring G c ∧
      (∀ f : G.edgeSet, fixed f → 2 ≤ (q f).val) ∧
      ((Finset.univ : Finset G.edgeSet).filter fun f => 2 ≤ (q f).val ∧ ¬ fixed f).card = t ∧
      ∃ H : SimpleGraph G.edgeSet, H.IsAcyclic ∧
        ∀ e f : G.edgeSet, H.Adj e f ↔ G.lineGraph.Adj e f ∧
          ((2 ≤ (q e).val) ↔ (2 ≤ (q f).val)) := by
  classical
  intro fixed
  have hG' : ∀ x y, G.Adj x y ↔ in1025_adj x y := hG
  have hne : ∀ {p q r : ZMod t × Fin 14}, G.Adj p q → G.Adj p r → q ≠ r → q.2 ≠ r.2 :=
    fun hq hr hqr h => hqr (in1025_inj hG' hq hr h)
  let q : G.lineGraph.Coloring (Fin 4) := SimpleGraph.Coloring.mk (fun f => in1025_qL f.1) (by
    intro e f h
    obtain ⟨v, a, b, ha, hb, hab, he, hf⟩ := in1025_line_adj h
    show in1025_qL e.1 ≠ in1025_qL f.1
    rw [he, hf]
    exact in1025_base_proper v.2 a.2 (in1025_lab hG' ha) b.2 (in1025_lab hG' hb) (hne ha hb hab))
  have hq : ∀ f : G.edgeSet, q f = in1025_qL f.1 := fun f => rfl
  let M : Finset G.edgeSet := Finset.univ.filter (fun f => in1025_mL f.1 = true)
  let c : G.lineGraph.Coloring (Fin 5) := SimpleGraph.Coloring.mk (fun f => in1025_cL f.1) (by
    intro e f h
    obtain ⟨v, a, b, ha, hb, hab, he, hf⟩ := in1025_line_adj h
    show in1025_cL e.1 ≠ in1025_cL f.1
    rw [he, hf]
    exact in1025_base_cproper v.2 a.2 (in1025_lab hG' ha) b.2 (in1025_lab hG' hb) (hne ha hb hab))
  have hc : ∀ f : G.edgeSet, c f = in1025_cL f.1 := fun f => rfl
  refine ⟨q, M, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- M is a matching
    intro e he f hf hef hadj
    obtain ⟨v, a, b, ha, hb, hab, he', hf'⟩ := in1025_line_adj hadj
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
    rw [he'] at he
    rw [hf'] at hf
    exact in1025_base_match v.2 a.2 (in1025_lab hG' ha) b.2 (in1025_lab hG' hb) (hne ha hb hab)
      ⟨he, hf⟩
  · -- c is the recolouring
    intro f
    rw [hc, hq]
    rcases f with ⟨z, hz⟩
    induction z using Sym2.ind with
    | h x y =>
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
      show in1025_cF x.2 y.2 = if in1025_mB x.2 y.2 = true then 4 else _
      unfold in1025_cF
      split_ifs <;> rfl
  · -- rich neighbours
    intro e _
    rcases e with ⟨w, hw⟩
    induction w using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := hw
      rcases in1025_base_rich x.2 y.2 (in1025_lab hG' hxy) with ⟨o, ho, hoy, hr⟩ | ⟨o, ho, hox, hr⟩
      · obtain ⟨z, hxz, hz2⟩ := in1025_exists_nbr hG' x o ho
        rw [← hz2] at hr hoy
        have hyz : y ≠ z := fun h => hoy (by rw [h])
        obtain ⟨hadj, hrich⟩ := in1025_rich_at hG' c hc hxy hxz hyz hr
        exact ⟨_, hadj, hrich⟩
      · obtain ⟨z, hyz', hz2⟩ := in1025_exists_nbr hG' y o ho
        rw [← hz2] at hr hox
        have hxz : x ≠ z := fun h => hox (by rw [h])
        obtain ⟨hadj, hrich⟩ := in1025_rich_at hG' c hc hxy.symm hyz' hxz hr
        have heq : (⟨s(x, y), hw⟩ : G.edgeSet) = ⟨s(y, x), hxy.symm⟩ := Subtype.ext Sym2.eq_swap
        rw [heq]
        exact ⟨_, hadj, hrich⟩
  · -- fixed edges are high
    rintro f ⟨i, u, v, huv, hf⟩
    rw [hq, hf]
    exact in1025_base_fix u v huv
  · -- exactly t further high edges
    let emb : ZMod t → G.edgeSet := fun i =>
      ⟨s((i, 2), (i, 13)), (hG' _ _).2 (Or.inl ⟨rfl, Or.inl (show ((2 : Fin 14).val, (13 : Fin 14).val) ∈ in1025_int by decide)⟩)⟩
    have hinj : Function.Injective emb := by
      intro i j h
      have h' := congrArg Subtype.val h
      simp only [emb, Sym2.eq_iff, Prod.mk.injEq] at h'
      rcases h' with ⟨⟨h1, -⟩, -⟩ | ⟨⟨-, h2⟩, -⟩
      · exact h1
      · exact absurd h2 (by decide)
    have hset : (Finset.univ : Finset G.edgeSet).filter (fun f => 2 ≤ (q f).val ∧ ¬ fixed f) =
        Finset.univ.image emb := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hhi, hnf⟩
        rcases f with ⟨w, hw⟩
        induction w using Sym2.ind with
        | h x y =>
          have hxy : G.Adj x y := hw
          rw [hq] at hhi
          change 2 ≤ (in1025_qF x.2 y.2).val at hhi
          rcases in1025_base_high x.2 y.2 (in1025_lab hG' hxy) hhi with hfix | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exfalso
            apply hnf
            have hcopy := in1025_same_copy hG' hxy (in1025_base_fix_int _ _ hfix)
            refine ⟨x.1, x.2, y.2, hfix, ?_⟩
            show s(x, y) = s((x.1, x.2), (x.1, y.2))
            exact congrArg₂ (fun a b => s(a, b)) (Prod.ext rfl rfl) (Prod.ext hcopy.symm rfl)
          · have hcopy := in1025_same_copy hG' hxy (by rw [h1, h2]; decide)
            refine ⟨x.1, Subtype.ext ?_⟩
            show s((x.1, 2), (x.1, 13)) = s(x, y)
            exact congrArg₂ (fun a b => s(a, b)) (Prod.ext rfl h1.symm) (Prod.ext hcopy h2.symm)
          · have hcopy := in1025_same_copy hG' hxy (by rw [h1, h2]; decide)
            refine ⟨x.1, Subtype.ext ?_⟩
            show s((x.1, 2), (x.1, 13)) = s(x, y)
            rw [Sym2.eq_swap]
            exact congrArg₂ (fun a b => s(a, b)) (Prod.ext rfl h1.symm) (Prod.ext hcopy h2.symm)
      · rintro ⟨i, rfl⟩
        refine ⟨(show 2 ≤ (in1025_qF 2 13).val by decide), ?_⟩
        rintro ⟨i', u, v, huv, hf⟩
        have hf' : s((i, (2 : Fin 14)), (i, 13)) = s((i', u), (i', v)) := hf
        rw [Sym2.eq_iff] at hf'
        rcases hf' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [Prod.mk.injEq] at h1 h2
          rw [← h1.2, ← h2.2] at huv
          exact absurd huv (by decide)
        · rw [Prod.mk.injEq] at h1 h2
          rw [← h1.2, ← h2.2] at huv
          exact absurd huv (by decide)
    rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  · -- the equal-class graph is acyclic
    let H : SimpleGraph G.edgeSet :=
      { Adj := fun e f => G.lineGraph.Adj e f ∧ ((2 ≤ (q e).val) ↔ (2 ≤ (q f).val))
        symm := ⟨fun e f h => ⟨h.1.symm, h.2.symm⟩⟩
        loopless := ⟨fun e h => h.1.ne rfl⟩ }
    refine ⟨H, ?_, fun e f => Iff.rfl⟩
    apply in1025_acyclic_of_rank H (fun f => in1025_rL f.1)
    · intro e f h
      obtain ⟨v, a, b, ha, hb, hab, he, hf⟩ := in1025_line_adj h.1
      have hcl := h.2
      rw [hq, hq, he, hf] at hcl
      show in1025_rL e.1 ≠ in1025_rL f.1
      rw [he, hf]
      exact in1025_base_rne v.2 a.2 (in1025_lab hG' ha) b.2 (in1025_lab hG' hb) (hne ha hb hab) hcl
    · intro x y z hxy hxz hy hz
      obtain ⟨v, a, b, ha, hb, hab, hx1, hy1⟩ := in1025_line_adj hxy.1
      obtain ⟨v', a', b', ha', hb', hab', hx2, hz1⟩ := in1025_line_adj hxz.1
      have hc1 := hxy.2
      have hc2 := hxz.2
      rw [hq, hq, hx1, hy1] at hc1
      have hy' : in1025_rL y.1 < in1025_rL x.1 := hy
      have hz' : in1025_rL z.1 < in1025_rL x.1 := hz
      rw [hx1, hy1] at hy'
      have hx12 : s(v, a) = s(v', a') := hx1.symm.trans hx2
      rcases Sym2.eq_iff.1 hx12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        rw [hq, hq, hx1, hz1] at hc2
        rw [hx1, hz1] at hz'
        by_cases hbb : b.2 = b'.2
        · have := in1025_inj hG' hb hb' hbb
          subst this
          exact Subtype.ext (hy1.trans hz1.symm)
        · exact (in1025_base_rone1 v.2 a.2 (in1025_lab hG' ha) b.2 (in1025_lab hG' hb) b'.2
            (in1025_lab hG' hb') (hne ha hb hab) (hne ha hb' hab') hbb hc1 hc2 hy' hz').elim
      · subst h1; subst h2
        rw [hq, hq, hx1, hz1] at hc2
        rw [hx1, hz1] at hz'
        exact (in1025_base_rone2 v.2 a.2 (in1025_lab hG' ha) b.2 (in1025_lab hG' hb) b'.2
          (in1025_lab hG' hb') (hne hb ha (Ne.symm hab)) (hne hb' ha.symm (Ne.symm hab')) hc1
          hc2 hy' hz').elim
