import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalFamilyMemberDepth
import AFTD.Kb.Tcs.IsCorrectIntervalFamily
import AFTD.Kb.Tcs.HasContiguousSubtrees
import AFTD.Kb.Tcs.InstFintypeColoredRootedTree
import AFTD.Kb.Tcs.InstFintypeIntervalFamily
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.NearestAncestorOfColor
import AFTD.Kb.Tcs.InstDecEqColoredRootedTree
import AFTD.Kb.Tcs.ColoredTreeSubtree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.InstPartialOrderColoredRootedTree
import AFTD.Kb.Tcs.InstDecEqIntervalFamily
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.V

/-!
# contiguous_interval_family_depth_lower_bound

Topic: data_structures   Node: 3e41faf3dc92

Provenance: formalization of a published result. Source: arXiv:2611.03620 (Adjacency Labeling Schemes of Size log n + O(log log* n) for Graphs of Bounded Treewidth), Proposition 3.3 (first sentence; the consequence depth ≥ log n / log(2R+1) − O(1) is not stated). Uses the knowledge base's ColoredRootedTree (4 colors = k = 3), IntervalFamily (at most R intervals per vertex), is_correct_interval_family and has_contiguous_subtrees.

For all integers R ≥ 1 and d ≥ 0 there is a finite rooted tree, properly colored with the 4 colors 0..3, with at most 11(2R+1)^d vertices, such that every correct interval family for it (an injective placement of the vertices in ℤ and a laminar family of nonempty integer intervals, each owned by a vertex and colored by its owner's color, such that for every vertex x and color c ≠ color(x) whose nearest proper ancestor of color c is u, some interval owned by u contains x's position and is contained in every interval of color c containing that position) in which every vertex owns at most R intervals and every subtree occupies consecutive positions has a member of depth at least d + 1 (contained in at least d + 1 members of its own color, itself included).
-/

/-- A vertex `c` of color 0 heading a unit of level `t`: level 0 has a descendant whose nearest
ancestor of color 0 is `c`; level `t+1` has `m` vertices above `c` with pairwise disjoint
subtrees, each containing a vertex whose nearest ancestor of color 0 is `c` and the head of a
unit of level `t`. -/
inductive cif_is_unit (T : ColoredRootedTree) (m : ℕ) : ℕ → T.V → Prop
  | zero (c w : T.V) (hw : T.color w ≠ 0) (hn : nearest_ancestor_of_color T w 0 c) :
      cif_is_unit T m 0 c
  | succ (t : ℕ) (c : T.V) (u x cc : Fin m → T.V)
      (hcu : ∀ i, c < u i)
      (hu : ∀ i j, i ≠ j → ∀ z : T.V, u i ≤ z → u j ≤ z → False)
      (hx : ∀ i, u i ≤ x i) (hxc : ∀ i, T.color (x i) ≠ 0)
      (hxn : ∀ i, nearest_ancestor_of_color T (x i) 0 c)
      (hcc : ∀ i, u i ≤ cc i) (hrec : ∀ i, cif_is_unit T m t (cc i)) :
      cif_is_unit T m (t + 1) c


/-- Vertices of the lower-bound tree of level `t`. -/
def cif_V (m : ℕ) : ℕ → Type
  | 0 => Option Unit
  | t + 1 => Option (Fin m × Option (Option (cif_V m t)))

def cif_V.fintype (m : ℕ) : (t : ℕ) → Fintype (cif_V m t)
  | 0 => (inferInstance : Fintype (Option Unit))
  | t + 1 => letI := cif_V.fintype m t
      (inferInstance : Fintype (Option (Fin m × Option (Option (cif_V m t)))))

def cif_V.decEq (m : ℕ) : (t : ℕ) → DecidableEq (cif_V m t)
  | 0 => (inferInstance : DecidableEq (Option Unit))
  | t + 1 => letI := cif_V.decEq m t
      (inferInstance : DecidableEq (Option (Fin m × Option (Option (cif_V m t)))))

def cif_V.le (m : ℕ) : (t : ℕ) → cif_V m t → cif_V m t → Prop
  | 0, none, _ => True
  | 0, some _, none => False
  | 0, some _, some _ => True
  | _ + 1, none, _ => True
  | _ + 1, some _, none => False
  | _ + 1, some (i, none), some (j, _) => i = j
  | _ + 1, some (_, some _), some (_, none) => False
  | _ + 1, some (i, some none), some (j, some none) => i = j
  | _ + 1, some (_, some none), some (_, some (some _)) => False
  | _ + 1, some (_, some (some _)), some (_, some none) => False
  | t + 1, some (i, some (some v)), some (j, some (some w)) => i = j ∧ cif_V.le m t v w

def cif_V.color (m : ℕ) : (t : ℕ) → cif_V m t → Fin 4
  | 0, none => 0
  | 0, some _ => 2
  | _ + 1, none => 0
  | _ + 1, some (_, none) => 1
  | _ + 1, some (_, some none) => 2
  | t + 1, some (_, some (some v)) => cif_V.color m t v

def cif_V.root (m : ℕ) : (t : ℕ) → cif_V m t
  | 0 => none
  | _ + 1 => none

theorem cif_V.le_refl (m : ℕ) : ∀ t (v : cif_V m t), cif_V.le m t v v := by
  intro t
  induction t with
  | zero => rintro (_ | _) <;> simp [cif_V.le]
  | succ t ih => rintro (_ | ⟨i, _ | _ | v⟩) <;> simp [cif_V.le, ih]

theorem cif_V.le_trans (m : ℕ) : ∀ t (a b c : cif_V m t), cif_V.le m t a b → cif_V.le m t b c →
    cif_V.le m t a c := by
  intro t
  induction t with
  | zero => rintro (_ | _) (_ | _) (_ | _) <;> simp [cif_V.le]
  | succ t ih =>
    rintro (_ | ⟨i, _ | _ | a⟩) (_ | ⟨j, _ | _ | b⟩) (_ | ⟨k, _ | _ | c⟩) <;> simp [cif_V.le] <;>
      first
      | (rintro rfl h2 rfl h4; exact ⟨rfl, ih _ _ _ h2 h4⟩)
      | (intros; subst_vars; simp_all)

theorem cif_V.le_antisymm (m : ℕ) : ∀ t (a b : cif_V m t), cif_V.le m t a b → cif_V.le m t b a →
    a = b := by
  intro t
  induction t with
  | zero => rintro (_ | ⟨⟨⟩⟩) (_ | ⟨⟨⟩⟩) <;> simp [cif_V.le] <;> rfl
  | succ t ih =>
    rintro (_ | ⟨i, _ | _ | a⟩) (_ | ⟨j, _ | _ | b⟩) <;> simp [cif_V.le] <;>
      first
      | rfl
      | (rintro rfl _; rfl)
      | (rintro rfl h2 _ h4; rw [ih _ _ h2 h4])

theorem cif_V.bot_le (m : ℕ) : ∀ t (v : cif_V m t), cif_V.le m t (cif_V.root m t) v := by
  intro t; cases t <;> intro v <;> simp [cif_V.root, cif_V.le]

theorem cif_V.color_root (m : ℕ) : ∀ t, cif_V.color m t (cif_V.root m t) = 0 := by
  intro t; cases t <;> simp [cif_V.root, cif_V.color]

theorem cif_V.down_chain (m : ℕ) : ∀ t (a b v : cif_V m t), cif_V.le m t a v → cif_V.le m t b v →
    cif_V.le m t a b ∨ cif_V.le m t b a := by
  intro t
  induction t with
  | zero => rintro (_ | _) (_ | _) (_ | _) <;> simp [cif_V.le]
  | succ t ih =>
    rintro (_ | ⟨i, _ | _ | a⟩) (_ | ⟨j, _ | _ | b⟩) (_ | ⟨k, _ | _ | v⟩) <;> simp [cif_V.le] <;>
      first
      | (rintro rfl h2 rfl h4; rcases ih _ _ _ h2 h4 with h | h <;> simp [h])
      | (intros; subst_vars; simp_all)

/-- An interval with endpoints outside a range `[a', b']` meeting it contains it. -/
theorem cif_icc_sub {a b a' b' q : ℤ} (hq : q ∈ Set.Icc a b) (hq' : q ∈ Set.Icc a' b')
    (ha : a ∉ Set.Icc a' b') (hb : b ∉ Set.Icc a' b') : Set.Icc a' b' ⊆ Set.Icc a b := by
  intro z hz
  simp only [Set.mem_Icc] at *
  constructor
  · by_contra h; push Not at h; exact ha ⟨by omega, by omega⟩
  · by_contra h; push Not at h; exact hb ⟨by omega, by omega⟩

open Classical in
/-- The induction of the lower bound: a unit of level `t` headed by `c` has a position in the
range of its subtree lying in `t + 1` members of color 0 owned by vertices of the subtree. -/
theorem cif_unit_count {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R)
    (hF : is_correct_interval_family F) (hC : has_contiguous_subtrees F) :
    ∀ (t : ℕ) (c : T.V), cif_is_unit T (2 * R + 1) t c →
      ∃ p : ℤ, p ∈ F.id '' colored_tree_subtree T c ∧
        t + 1 ≤ (Finset.univ.filter (fun j : F.ι => T.color (F.owner j) = 0 ∧ c ≤ F.owner j ∧
          p ∈ F.interval j)).card := by
  intro t c h
  induction h with
  | zero c w hw hn =>
    obtain ⟨i, hic, hio, hip, -⟩ := hF w 0 c (Ne.symm hw) hn
    refine ⟨F.id w, ⟨w, hn.1.le, rfl⟩, ?_⟩
    rw [Nat.zero_add, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨i, by simp [hio, hip, hn.2.1]⟩
  | succ t c u x cc hcu hu hx hxc hxn hcc hrec ih =>
    -- ranges of the subtrees of the `u i`
    have hQ : ∀ i, ∃ a b : ℤ, F.id '' colored_tree_subtree T (u i) = Set.Icc a b := fun i => hC (u i)
    choose qa qb hqab using hQ
    -- endpoints of the members owned by `c`
    have hE : ∀ j : F.ι, ∃ a b : ℤ, a ≤ b ∧ F.interval j = Set.Icc a b := F.interval_icc
    choose ea eb heab heq using hE
    set K := Finset.univ.filter (fun j : F.ι => F.owner j = c) with hK
    set Ep := K.image ea ∪ K.image eb with hEp
    have hEpc : Ep.card ≤ 2 * R := by
      have h1 : Ep.card ≤ (K.image ea).card + (K.image eb).card := Finset.card_union_le _ _
      have h2 := Finset.card_image_le (s := K) (f := ea)
      have h3 := Finset.card_image_le (s := K) (f := eb)
      have h4 : K.card ≤ R := F.owner_bound c
      omega
    -- some range contains no endpoint
    have hfree : ∃ i, ∀ e ∈ Ep, e ∉ Set.Icc (qa i) (qb i) := by
      by_contra hno
      push Not at hno
      choose f hfE hfQ using hno
      obtain ⟨i, -, j, -, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := (Finset.univ : Finset (Fin (2 * R + 1)))) (t := Ep)
        (by simp; omega) (fun i _ => hfE i)
      have hi := hfQ i
      have hj := hfQ j
      rw [← hqab] at hi
      rw [← hqab, ← hfij] at hj
      obtain ⟨zi, hzi, hzi'⟩ := hi
      obtain ⟨zj, hzj, hzj'⟩ := hj
      have : zi = zj := F.id_inj (hzi'.trans hzj'.symm)
      subst this
      exact hu i j hij zi hzi hzj
    obtain ⟨i, hi⟩ := hfree
    obtain ⟨i0, hi0c, hi0o, hi0p, -⟩ := hF (x i) 0 c (Ne.symm (hxc i)) (hxn i)
    have hxQ : F.id (x i) ∈ Set.Icc (qa i) (qb i) := by
      rw [← hqab]; exact ⟨x i, hx i, rfl⟩
    have hK0 : i0 ∈ K := by simp [hK, hi0o]
    have hsub : Set.Icc (qa i) (qb i) ⊆ F.interval i0 := by
      rw [heq i0] at hi0p ⊢
      exact cif_icc_sub hi0p hxQ (hi _ (by simp [hEp]; left; exact ⟨i0, hK0, rfl⟩))
        (hi _ (by simp [hEp]; right; exact ⟨i0, hK0, rfl⟩))
    obtain ⟨p, ⟨z, hz, rfl⟩, hcard⟩ := ih i
    have hzc : c < z := lt_of_lt_of_le (lt_of_lt_of_le (hcu i) (hcc i)) hz
    have hpQ : F.id z ∈ Set.Icc (qa i) (qb i) := by
      rw [← hqab]; exact ⟨z, le_trans (hcc i) hz, rfl⟩
    refine ⟨F.id z, ⟨z, hzc.le, rfl⟩, ?_⟩
    have hcc' : c < cc i := lt_of_lt_of_le (hcu i) (hcc i)
    have hnot : i0 ∉ Finset.univ.filter (fun j : F.ι => T.color (F.owner j) = 0 ∧ cc i ≤ F.owner j ∧
          F.id z ∈ F.interval j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi0o]
      rintro ⟨-, hle, -⟩
      exact absurd hle (not_le_of_gt hcc')
    calc t + 1 + 1 ≤ (insert i0 (Finset.univ.filter (fun j : F.ι => T.color (F.owner j) = 0 ∧
            cc i ≤ F.owner j ∧ F.id z ∈ F.interval j))).card := by
          rw [Finset.card_insert_of_notMem hnot]; omega
      _ ≤ _ := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          rcases hj with rfl | ⟨h1, h2, h3⟩
          · exact ⟨hi0c, hi0o.ge, hsub hpQ⟩
          · exact ⟨h1, le_trans hcc'.le h2, h3⟩

open Classical in
/-- `t + 1` members of color 0 sharing a position give a member of depth at least `t + 1`. -/
theorem cif_depth_of_count {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R) (c : T.V)
    (p : ℤ) (t : ℕ)
    (h : t + 1 ≤ (Finset.univ.filter (fun j : F.ι => T.color (F.owner j) = 0 ∧ c ≤ F.owner j ∧
          p ∈ F.interval j)).card) :
    ∃ i : F.ι, t + 1 ≤ interval_family_member_depth F i := by
  classical
  set S := Finset.univ.filter (fun j : F.ι => T.color (F.owner j) = 0 ∧ c ≤ F.owner j ∧
          p ∈ F.interval j) with hS
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hjS, hjmin⟩ := Finset.exists_min_image S (fun k => (F.interval k).ncard) hne
  have hjS' := hjS
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hjS'
  have hfin : ∀ k, (F.interval k).Finite := by
    intro k; obtain ⟨a, b, -, hab⟩ := F.interval_icc k; rw [hab]; exact Set.finite_Icc a b
  refine ⟨j, ?_⟩
  unfold interval_family_member_depth
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine le_trans h (Finset.card_le_card ?_)
  intro k hk
  have hk' := hk
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
  refine ⟨by rw [hk'.1, hjS'.1], ?_⟩
  rcases F.laminar j k with h1 | h1 | h1
  · exact h1
  · have := hjmin k hk
    rw [Set.eq_of_subset_of_ncard_le h1 this (hfin j)]
  · exact absurd (Set.disjoint_left.mp h1 hjS'.2.2) (not_not.mpr hk'.2.2)

def cif_V.po (m t : ℕ) : PartialOrder (cif_V m t) where
  le := cif_V.le m t
  le_refl := cif_V.le_refl m t
  le_trans := cif_V.le_trans m t
  le_antisymm := cif_V.le_antisymm m t

theorem cif_V.not_cover (m : ℕ) : ∀ t (u v : cif_V m t), cif_V.le m t u v → ¬ cif_V.le m t v u →
    cif_V.color m t u = cif_V.color m t v →
    ∃ w, cif_V.le m t u w ∧ cif_V.le m t w v ∧ ¬ cif_V.le m t v w ∧ w ≠ u := by
  intro t
  induction t with
  | zero => rintro (_ | ⟨⟨⟩⟩) (_ | ⟨⟨⟩⟩) <;> simp [cif_V.le, cif_V.color]
  | succ t ih =>
    rintro (_ | ⟨i, _ | _ | a⟩) (_ | ⟨j, _ | _ | b⟩) <;> simp [cif_V.le, cif_V.color]
    · intro _; exact ⟨some (j, none), by simp [cif_V.le], by simp [cif_V.le], fun h => by cases h⟩
    · rintro rfl h; exact absurd rfl h
    · rintro rfl hb
      refine ⟨some (i, some (some (cif_V.root m t))), by simp [cif_V.le],
        by simp [cif_V.le, cif_V.bot_le], ?_, fun h => by cases h⟩
      intro h0
      have h : cif_V.le m t b (cif_V.root m t) := h0.2
      have := cif_V.le_antisymm m t _ _ h (cif_V.bot_le m t b)
      subst this
      rw [cif_V.color_root] at hb
      exact absurd hb (by decide)
    · rintro rfl h; exact absurd rfl h
    · rintro rfl hab hba hc
      obtain ⟨w, h1, h2, h3, h4⟩ := ih a b hab (hba rfl) hc
      exact ⟨some (i, some (some w)), by simp [cif_V.le, h1], by simp [cif_V.le, h2],
        by simp [cif_V.le, h3], fun h => h4 (by cases h; rfl)⟩

/-- The lower-bound tree of level `t` with `m` branches per unit. -/
def cif_tree (m t : ℕ) : ColoredRootedTree where
  V := cif_V m t
  fintype := cif_V.fintype m t
  decEq := cif_V.decEq m t
  partialOrder := cif_V.po m t
  root := cif_V.root m t
  bot_le := cif_V.bot_le m t
  down_chain := cif_V.down_chain m t
  color := cif_V.color m t
  proper_coloring := by
    letI := cif_V.po m t
    intro u v huv hcov hcol
    obtain ⟨w, h1, h2, h3, h4⟩ :=
      cif_V.not_cover m t u v (lt_iff_le_not_ge.mp huv).1 (lt_iff_le_not_ge.mp huv).2 hcol
    exact h4 (hcov w h1 (lt_iff_le_not_ge.mpr ⟨h2, h3⟩))

theorem cif_le_iff {m t : ℕ} (a b : (cif_tree m t).V) : a ≤ b ↔ cif_V.le m t a b := Iff.rfl

theorem cif_lt_iff {m t : ℕ} (a b : (cif_tree m t).V) :
    a < b ↔ cif_V.le m t a b ∧ ¬ cif_V.le m t b a := lt_iff_le_not_ge

theorem cif_tree_color {m t : ℕ} (a : (cif_tree m t).V) : (cif_tree m t).color a = cif_V.color m t a := rfl

theorem cif_tree_root {m t : ℕ} : (cif_tree m t).root = cif_V.root m t := rfl

/-- Units transfer along a color-preserving order embedding whose image is an up-set over the root. -/
theorem cif_is_unit_map {T1 T2 : ColoredRootedTree} (m : ℕ) (φ : T1.V → T2.V)
    (hle : ∀ a b, φ a ≤ φ b ↔ a ≤ b) (hcol : ∀ a, T2.color (φ a) = T1.color a)
    (hconv : ∀ z, φ T1.root ≤ z → ∃ v, z = φ v) :
    ∀ t c, cif_is_unit T1 m t c → cif_is_unit T2 m t (φ c) := by
  have hlt : ∀ a b, φ a < φ b ↔ a < b := by
    intro a b; rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle, hle]
  have hnear : ∀ w c, nearest_ancestor_of_color T1 w 0 c → nearest_ancestor_of_color T2 (φ w) 0 (φ c) := by
    rintro w c ⟨h1, h2, h3⟩
    refine ⟨(hlt _ _).mpr h1, by rw [hcol]; exact h2, fun z hz1 hz2 => ?_⟩
    obtain ⟨v, rfl⟩ := hconv z (le_trans ((hle _ _).mpr (T1.bot_le c)) hz1.le)
    rw [hcol]; exact h3 v ((hlt _ _).mp hz1) ((hlt _ _).mp hz2)
  intro t c h
  induction h with
  | zero c w hw hn => exact cif_is_unit.zero _ (φ w) (by rw [hcol]; exact hw) (hnear w c hn)
  | succ t c u x cc hcu hu hx hxc hxn hcc hrec ih =>
    refine cif_is_unit.succ t (φ c) (fun i => φ (u i)) (fun i => φ (x i)) (fun i => φ (cc i))
      (fun i => (hlt _ _).mpr (hcu i)) ?_ (fun i => (hle _ _).mpr (hx i))
      (fun i => by rw [hcol]; exact hxc i) (fun i => hnear _ _ (hxn i))
      (fun i => (hle _ _).mpr (hcc i)) ih
    intro i j hij z hz1 hz2
    obtain ⟨v, rfl⟩ := hconv z (le_trans ((hle _ _).mpr (T1.bot_le (u i))) hz1)
    exact hu i j hij v ((hle _ _).mp hz1) ((hle _ _).mp hz2)

/-- The copy of the level-`t` tree hanging below branch `i`. -/
def cif_emb (m t : ℕ) (i : Fin m) (v : cif_V m t) : cif_V m (t + 1) := some (i, some (some v))

theorem cif_root_unit (m : ℕ) : ∀ t, cif_is_unit (cif_tree m t) m t (cif_tree m t).root := by
  intro t
  induction t with
  | zero =>
    refine cif_is_unit.zero _ (some () : cif_V m 0) ?_ ⟨?_, ?_, ?_⟩
    · show cif_V.color m 0 (some ()) ≠ 0; simp [cif_V.color]
    · exact (cif_lt_iff _ _).mpr (by simp [cif_tree_root, cif_V.root, cif_V.le])
    · exact cif_V.color_root m 0
    · rintro (_ | ⟨⟨⟩⟩) h1 h2
      · exact absurd h1 (lt_irrefl _)
      · exact absurd h2 (lt_irrefl _)
  | succ t ih =>
    refine cif_is_unit.succ t _ (fun i => (some (i, none) : cif_V m (t + 1)))
      (fun i => (some (i, some none) : cif_V m (t + 1)))
      (fun i => cif_emb m t i (cif_V.root m t)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i; exact (cif_lt_iff _ _).mpr (by simp [cif_tree_root, cif_V.root, cif_V.le])
    · intro i j hij z h1 h2
      have h1' : cif_V.le m (t + 1) (some (i, none)) z := h1
      have h2' : cif_V.le m (t + 1) (some (j, none)) z := h2
      rcases z with _ | ⟨k, _ | _ | v⟩ <;> simp [cif_V.le] at h1' h2' <;>
        exact hij (h1'.trans h2'.symm)
    · intro i; show cif_V.le m (t + 1) (some (i, none)) (some (i, some none)); simp [cif_V.le]
    · intro i; show cif_V.color m (t + 1) (some (i, some none)) ≠ 0; simp [cif_V.color]
    · intro i
      refine ⟨(cif_lt_iff _ _).mpr (by simp [cif_tree_root, cif_V.root, cif_V.le]),
        cif_V.color_root m (t + 1), ?_⟩
      intro z h1 h2
      have h1' := (cif_lt_iff _ _).mp h1
      have h2' := (cif_lt_iff _ _).mp h2
      show cif_V.color m (t + 1) z ≠ 0
      rcases z with _ | ⟨k, _ | _ | v⟩ <;>
        simp [cif_tree_root, cif_V.root, cif_V.le, cif_V.color] at h1' h2' ⊢
    · intro i
      show cif_V.le m (t + 1) (some (i, none)) (cif_emb m t i (cif_V.root m t))
      simp [cif_emb, cif_V.le]
    · intro i
      refine cif_is_unit_map (T1 := cif_tree m t) (T2 := cif_tree m (t + 1)) m (cif_emb m t i) ?_ ?_ ?_ t _ ih
      · intro a b
        show cif_V.le m (t + 1) (cif_emb m t i a) (cif_emb m t i b) ↔ cif_V.le m t a b
        simp [cif_emb, cif_V.le]
      · intro a; rfl
      · intro z h
        have h' : cif_V.le m (t + 1) (cif_emb m t i (cif_V.root m t)) z := h
        rcases z with _ | ⟨k, _ | _ | v⟩ <;> simp [cif_emb, cif_V.le] at h'
        obtain ⟨rfl, -⟩ := h'
        exact ⟨v, rfl⟩

theorem cif_card (m : ℕ) (hm : 3 ≤ m) :
    ∀ t, @Fintype.card (cif_V m t) (cif_V.fintype m t) + 4 ≤ 6 * m ^ t := by
  intro t
  induction t with
  | zero =>
    show @Fintype.card (Option Unit) inferInstance + 4 ≤ 6 * m ^ 0
    simp
  | succ t ih =>
    have h : @Fintype.card (cif_V m (t + 1)) (cif_V.fintype m (t + 1))
        = m * (@Fintype.card (cif_V m t) (cif_V.fintype m t) + 2) + 1 := by
      show @Fintype.card (Option (Fin m × Option (Option (cif_V m t))))
        (letI := cif_V.fintype m t; inferInstance) = _
      simp [Fintype.card_option, Fintype.card_prod]
    rw [h, pow_succ]
    nlinarith

theorem contiguous_interval_family_depth_lower_bound (R d : ℕ) (hR : 1 ≤ R) :
    ∃ T : ColoredRootedTree, Fintype.card T.V ≤ 11 * (2 * R + 1) ^ d ∧
      ∀ F : IntervalFamily T R, is_correct_interval_family F → has_contiguous_subtrees F →
        ∃ i : F.ι, d + 1 ≤ interval_family_member_depth F i := by
  refine ⟨cif_tree (2 * R + 1) d, ?_, ?_⟩
  · have := cif_card (2 * R + 1) (by omega) d
    show @Fintype.card (cif_V (2 * R + 1) d) (cif_V.fintype (2 * R + 1) d) ≤ _
    omega
  · intro F hF hC
    obtain ⟨p, -, hp⟩ := cif_unit_count F hF hC d _ (cif_root_unit (2 * R + 1) d)
    exact cif_depth_of_count F _ p d hp
