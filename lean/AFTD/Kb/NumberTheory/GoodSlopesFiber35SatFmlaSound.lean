import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_fiber35_sat_fmla_sound

Topic: elementary_number_theory   Node: a69efa212d21

Provenance: helper lemma. helper for good_slopes_fiber35_anchored_width_gap (OP-1027 route)

Soundness of a clause checker for the 35-point good-slopes SAT model: if every clause of a CNF formula passes the checker (anchor, at-most-one and cover clauses of good directions, four points on a fiber or on the line y + x = 0, six good neighbours of a bad direction, eight bad directions, or an assumed good/bad direction), then the valuation read off a point set S and a direction set G satisfies the formula, provided S and G satisfy the corresponding hypotheses.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

open Lean Elab Command in
elab "w35_lrat_core " nm:ident ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  Command.liftTermElabM do
    let cnf ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    let (_,ctx,_,proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat nm.getId
    addDecl <| Declaration.defnDecl {
      name := nm.getId ++ `formula, levelParams := [], type := mkConst ``Sat.Fmla, value := ctx,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    addDecl <| Declaration.thmDecl {
      name := nm.getId ++ `sat_proof, levelParams := [], type := ← Meta.inferType proof, value := proof }

namespace W35

def U : List (ZMod 35) := [1,2,3,4,6,8,9,11,12,13,16,17,18,19,22,23,24,26,27,29,31,32,33,34]

def pt (i : ℕ) : ZMod 35 × ZMod 35 := (((i / 35 : ℕ) : ZMod 35), ((i % 35 : ℕ) : ZMod 35))
def idx (p : ZMod 35 × ZMod 35) : ℕ := 35 * p.1.val + p.2.val
def gidx (a : ZMod 35) : ℕ := 1225 + U.idxOf a

def val (S : Finset (ZMod 35 × ZMod 35)) (G : Finset (ZMod 35)) : Sat.Valuation :=
  fun i => if i < 1225 then pt i ∈ S else U.getD (i - 1225) 0 ∈ G

def leq : Sat.Literal → Sat.Literal → Bool
  | .pos i, .pos j => i == j
  | .neg i, .neg j => i == j
  | _, _ => false

theorem mem_of_any (c : Sat.Clause) (l : Sat.Literal) (h : List.any c (leq l) = true) :
    List.Mem l c := by
  change List Sat.Literal at c
  induction c with
  | nil => simp at h
  | cons a as ih =>
    rw [List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · have : a = l := by
        cases a <;> cases l <;> simp_all [leq]
      subst this; exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

theorem sat_of (v : Sat.Valuation) (c : Sat.Clause)
    (h : (∀ l, List.Mem l c → v.neg l) → False) : v.satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h (fun l hl => by cases hl)
  | cons a as ih =>
    intro ha
    exact ih (fun hall => h (fun l hl => by
      cases hl with
      | head => exact ha
      | tail _ hl => exact hall l hl))

theorem sat_and {v : Sat.Valuation} {f g : Sat.Fmla} (hf : v.satisfies_fmla f)
    (hg : v.satisfies_fmla g) : v.satisfies_fmla (f.and g) :=
  ⟨fun c hc => by
    rcases List.mem_append.mp hc with h | h
    · exact hf.prop c h
    · exact hg.prop c h⟩

theorem sat_one {v : Sat.Valuation} {c : Sat.Clause} (h : v.satisfies c) :
    v.satisfies_fmla (Sat.Fmla.one c) :=
  ⟨fun c' hc' => by
    have hc : c' = c := List.mem_singleton.mp hc'
    simpa only [hc] using h⟩

theorem pt_idx (p : ZMod 35 × ZMod 35) : pt (idx p) = p := by
  have h1 := ZMod.val_lt p.1
  have h2 := ZMod.val_lt p.2
  have e1 : (35 * p.1.val + p.2.val) / 35 = p.1.val := by omega
  have e2 : (35 * p.1.val + p.2.val) % 35 = p.2.val := by omega
  unfold pt idx
  rw [e1, e2]
  simp

theorem idx_lt (p : ZMod 35 × ZMod 35) : idx p < 1225 := by
  have h1 := ZMod.val_lt p.1
  have h2 := ZMod.val_lt p.2
  unfold idx; omega

theorem val_pt (S G) (p : ZMod 35 × ZMod 35) : val S G (idx p) ↔ p ∈ S := by
  unfold val; rw [if_pos (idx_lt p), pt_idx]

theorem U_getD : ∀ a ∈ U, U.getD (U.idxOf a) 0 = a := by decide

theorem U_idx_lt : ∀ a ∈ U, U.idxOf a < 24 := by decide

theorem val_g (S G) (a : ZMod 35) (ha : a ∈ U) : val S G (gidx a) ↔ a ∈ G := by
  unfold val gidx
  rw [if_neg (by omega), Nat.add_sub_cancel_left, U_getD a ha]

theorem U_unit : ∀ a ∈ U, ∃ b : ZMod 35, a * b = 1 := by decide

theorem U_card : U.toFinset.card = 24 := by decide

theorem U_nodup : U.Nodup := by decide

section
variable (S : Finset (ZMod 35 × ZMod 35)) (G : Finset (ZMod 35))

theorem c_anchor (c : Sat.Clause) (p : ZMod 35 × ZMod 35) (hp : p ∈ S)
    (hm : List.any c (leq (.pos (idx p))) = true) : (val S G).satisfies c := by
  apply sat_of; intro hall
  exact hall _ (mem_of_any c _ hm) ((val_pt S G p).2 hp)

theorem c_amo (hG : ∀ a, a ∈ G → Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S)
    (c : Sat.Clause) (a : ZMod 35) (p q : ZMod 35 × ZMod 35) (ha : a ∈ U)
    (hpq : p ≠ q) (hf : p.2 + a * p.1 = q.2 + a * q.1)
    (m1 : List.any c (leq (.neg (gidx a))) = true)
    (m2 : List.any c (leq (.neg (idx p))) = true)
    (m3 : List.any c (leq (.neg (idx q))) = true) : (val S G).satisfies c := by
  apply sat_of; intro hall
  have h1 : val S G (gidx a) := hall _ (mem_of_any c _ m1)
  have h2 : val S G (idx p) := hall _ (mem_of_any c _ m2)
  have h3 : val S G (idx q) := hall _ (mem_of_any c _ m3)
  rw [val_g S G a ha] at h1
  rw [val_pt] at h2 h3
  exact hpq (hG a h1 h2 h3 hf)

theorem c_cover (hcov : ∀ a t, a ∈ G → ∃ p ∈ S, p.2 + a * p.1 = t)
    (c : Sat.Clause) (a t : ZMod 35) (ha : a ∈ U)
    (m1 : List.any c (leq (.neg (gidx a))) = true)
    (m2 : ∀ x : ZMod 35, List.any c (leq (.pos (idx (x, t - a * x)))) = true) :
    (val S G).satisfies c := by
  apply sat_of; intro hall
  have h1 : val S G (gidx a) := hall _ (mem_of_any c _ m1)
  rw [val_g S G a ha] at h1
  obtain ⟨p, hp, hpt⟩ := hcov a t h1
  have hpe : (p.1, t - a * p.1) = p := by
    ext
    · rfl
    · simp only; rw [← hpt]; ring
  have h2 := hall _ (mem_of_any c _ (m2 p.1))
  change ¬ val S G (idx (p.1, t - a * p.1)) at h2
  rw [val_pt, hpe] at h2
  exact h2 hp

theorem c_four (P : ZMod 35 × ZMod 35 → Prop) [DecidablePred P] (hP : (S.filter P).card ≤ 3)
    (c : Sat.Clause) (L : List (ZMod 35 × ZMod 35)) (hL : L.Nodup) (hlen : L.length = 4)
    (hPL : ∀ p ∈ L, P p)
    (hm : ∀ p ∈ L, List.any c (leq (.neg (idx p))) = true) : (val S G).satisfies c := by
  apply sat_of; intro hall
  have hsub : L.toFinset ⊆ S.filter P := by
    intro p hp
    rw [List.mem_toFinset] at hp
    have h := hall _ (mem_of_any c _ (hm p hp))
    change val S G (idx p) at h
    rw [val_pt] at h
    exact Finset.mem_filter.mpr ⟨h, hPL p hp⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hL, hlen] at this
  omega

theorem c_nb (hnb : ∀ a : ZMod 35, IsUnit a → a ∉ G →
      (G.filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5)
    (c : Sat.Clause) (a : ZMod 35) (ha : a ∈ U) (L : List (ZMod 35)) (hL : L.Nodup)
    (hlen : L.length = 6) (hU : ∀ b ∈ L, b ∈ U)
    (hLa : ∀ b ∈ L, b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))
    (m1 : List.any c (leq (.pos (gidx a))) = true)
    (hm : ∀ b ∈ L, List.any c (leq (.neg (gidx b))) = true) : (val S G).satisfies c := by
  apply sat_of; intro hall
  have h1 : ¬ val S G (gidx a) := hall _ (mem_of_any c _ m1)
  rw [val_g S G a ha] at h1
  have hu : IsUnit a := by
    obtain ⟨b, hb⟩ := U_unit a ha
    exact IsUnit.of_mul_eq_one b hb
  have hsub : L.toFinset ⊆ G.filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7)) := by
    intro b hb
    rw [List.mem_toFinset] at hb
    have h := hall _ (mem_of_any c _ (hm b hb))
    change val S G (gidx b) at h
    rw [val_g S G b (hU b hb)] at h
    exact Finset.mem_filter.mpr ⟨h, hLa b hb⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hL, hlen] at this
  have := hnb a hu h1
  omega

theorem c_count (h17 : 17 ≤ G.card) (hGU : G ⊆ U.toFinset)
    (c : Sat.Clause) (L : List (ZMod 35)) (hL : L.Nodup) (hlen : L.length = 8)
    (hU : ∀ b ∈ L, b ∈ U)
    (hm : ∀ b ∈ L, List.any c (leq (.pos (gidx b))) = true) : (val S G).satisfies c := by
  apply sat_of; intro hall
  have hsub : G ⊆ U.toFinset \ L.toFinset := by
    intro b hb
    rw [Finset.mem_sdiff]
    refine ⟨hGU hb, fun hbL => ?_⟩
    rw [List.mem_toFinset] at hbL
    have h := hall _ (mem_of_any c _ (hm b hbL))
    change ¬ val S G (gidx b) at h
    rw [val_g S G b (hU b hbL)] at h
    exact h hb
  have hLU : L.toFinset ⊆ U.toFinset := by
    intro b hb; rw [List.mem_toFinset] at hb ⊢; exact hU b hb
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hLU, List.toFinset_card_of_nodup hL, hlen, U_card] at this
  omega

end

theorem good_sub (S : Finset (ZMod 35 × ZMod 35)) :
    good_slopes_point_directions 35 S ⊆ U.toFinset := by
  intro a ha
  unfold good_slopes_point_directions at ha
  rw [Finset.mem_filter] at ha
  obtain ⟨b, hb⟩ := ha.2.1.exists_right_inv
  have key : ∀ a b : ZMod 35, a * b = 1 → a ∈ U.toFinset := by decide
  exact key a b hb

theorem good_inj (S : Finset (ZMod 35 × ZMod 35)) :
    ∀ a, a ∈ good_slopes_point_directions 35 S →
      Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S := by
  intro a ha
  unfold good_slopes_point_directions at ha
  exact (Finset.mem_filter.mp ha).2.2

theorem good_cover (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35) :
    ∀ a t, a ∈ good_slopes_point_directions 35 S → ∃ p ∈ S, p.2 + a * p.1 = t := by
  intro a t ha
  have hinj := good_inj S a ha
  have himg : (S.image (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1)).card = 35 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have huniv : S.image (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [himg, ZMod.card])
  have ht : t ∈ S.image (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) := by
    rw [huniv]; exact Finset.mem_univ t
  obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp ht
  exact ⟨p, hp, hpt⟩

end W35

namespace W35

def gv (g : ℕ) : ZMod 35 := U.getD (g - 1225) 0

def rval (S : Finset (ZMod 35 × ZMod 35)) (G : Finset (ZMod 35)) : Sat.Valuation :=
  fun i => if i < 1225 then pt i ∈ S else gv i ∈ G

theorem rval_pt {S G} {i : ℕ} (hi : i < 1225) : rval S G i ↔ pt i ∈ S := by
  unfold rval; rw [if_pos hi]

theorem rval_g {S G} {g : ℕ} (hg : 1225 ≤ g) : rval S G g ↔ gv g ∈ G := by
  unfold rval; rw [if_neg (by omega)]

theorem gv_mem : ∀ k < 24, U.getD k 0 ∈ U := by decide

theorem gv_U {g : ℕ} (h1 : 1225 ≤ g) (h2 : g < 1249) : gv g ∈ U := by
  unfold gv; exact gv_mem (g - 1225) (by omega)

def chkAnchor (A : ZMod 35 × ZMod 35) : List Sat.Literal → Bool
  | [.pos i] => decide (i < 1225) && (decide (pt i = (0, 0)) || decide (pt i = A))
  | _ => false

def chkAmo : List Sat.Literal → Bool
  | [.neg g, .neg i, .neg j] =>
    decide (1225 ≤ g ∧ g < 1249 ∧ i < 1225 ∧ j < 1225 ∧ pt i ≠ pt j ∧
      (pt i).2 + gv g * (pt i).1 = (pt j).2 + gv g * (pt j).1)
  | _ => false

def chkCover : List Sat.Literal → Bool
  | .neg g :: .pos i :: rest =>
    decide (1225 ≤ g ∧ g < 1249 ∧ i < 1225) &&
      decide (∀ x : ZMod 35, List.any (.pos i :: rest)
        (leq (.pos (idx (x, ((pt i).2 + gv g * (pt i).1) - gv g * x)))) = true)
  | _ => false

def chkFour (P : ZMod 35 × ZMod 35 → Prop) [DecidablePred P] : List Sat.Literal → Bool
  | [.neg i1, .neg i2, .neg i3, .neg i4] =>
    decide (i1 < 1225 ∧ i2 < 1225 ∧ i3 < 1225 ∧ i4 < 1225 ∧
      [pt i1, pt i2, pt i3, pt i4].Nodup ∧ P (pt i1) ∧ P (pt i2) ∧ P (pt i3) ∧ P (pt i4))
  | _ => false

def chkWidth : List Sat.Literal → Bool
  | [.neg i1, .neg i2, .neg i3, .neg i4] =>
    chkFour (fun p => p.1 = (pt i1).1) [.neg i1, .neg i2, .neg i3, .neg i4]
  | _ => false

def nbRel (a b : ZMod 35) : Prop := b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7)

instance : DecidableRel nbRel := fun a b => by unfold nbRel; infer_instance

def chkNb : List Sat.Literal → Bool
  | [.pos ga, .neg b1, .neg b2, .neg b3, .neg b4, .neg b5, .neg b6] =>
    decide (1225 ≤ ga ∧ ga < 1249 ∧ ∀ b ∈ [b1, b2, b3, b4, b5, b6], 1225 ≤ b ∧ b < 1249) &&
    decide ([gv b1, gv b2, gv b3, gv b4, gv b5, gv b6].Nodup ∧
      ∀ b ∈ [gv b1, gv b2, gv b3, gv b4, gv b5, gv b6], nbRel (gv ga) b)
  | _ => false

def chkCount : List Sat.Literal → Bool
  | [.pos b1, .pos b2, .pos b3, .pos b4, .pos b5, .pos b6, .pos b7, .pos b8] =>
    decide (∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], 1225 ≤ b ∧ b < 1249) &&
    decide ([gv b1, gv b2, gv b3, gv b4, gv b5, gv b6, gv b7, gv b8].Nodup)
  | _ => false

def chkHyp (Gin Gout : List (ZMod 35)) : List Sat.Literal → Bool
  | [.pos g] => decide (1225 ≤ g ∧ gv g ∈ Gin)
  | [.neg g] => decide (1225 ≤ g ∧ gv g ∈ Gout)
  | _ => false

def chk (A : ZMod 35 × ZMod 35) (Gin Gout : List (ZMod 35)) (c : List Sat.Literal) : Bool :=
  chkAnchor A c || chkAmo c || chkCover c || chkWidth c ||
    chkFour (fun p => p.2 + p.1 = 0) c || chkNb c || chkCount c || chkHyp Gin Gout c

section
variable (S : Finset (ZMod 35 × ZMod 35)) (G : Finset (ZMod 35))

theorem s_anchor (A : ZMod 35 × ZMod 35) (h0 : (0, 0) ∈ S) (hA : A ∈ S)
    (c : List Sat.Literal) (h : chkAnchor A c = true) : (rval S G).satisfies c := by
  unfold chkAnchor at h
  split at h
  · rename_i i
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hi, hp⟩ := h
    apply sat_of; intro hall
    have h1 : ¬ rval S G i := hall _ (List.Mem.head _)
    rw [rval_pt hi] at h1
    rcases hp with hp | hp <;> rw [hp] at h1 <;> contradiction
  · simp at h

theorem s_amo (hG : ∀ a, a ∈ G → Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S)
    (c : List Sat.Literal) (h : chkAmo c = true) : (rval S G).satisfies c := by
  unfold chkAmo at h
  split at h
  · rename_i g i j
    simp only [decide_eq_true_eq] at h
    obtain ⟨hg1, hg2, hi, hj, hne, hf⟩ := h
    apply sat_of; intro hall
    have h1 : rval S G g := hall _ (List.Mem.head _)
    have h2 : rval S G i := hall _ (List.Mem.tail _ (List.Mem.head _))
    have h3 : rval S G j := hall _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    rw [rval_g hg1] at h1
    rw [rval_pt hi] at h2
    rw [rval_pt hj] at h3
    exact hne (hG _ h1 h2 h3 hf)
  · simp at h

theorem s_cover (hcov : ∀ a t, a ∈ G → ∃ p ∈ S, p.2 + a * p.1 = t)
    (c : List Sat.Literal) (h : chkCover c = true) : (rval S G).satisfies c := by
  unfold chkCover at h
  split at h
  · rename_i g i rest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hg1, hg2, hi⟩, hx⟩ := h
    apply sat_of; intro hall
    have h1 : rval S G g := hall _ (List.Mem.head _)
    rw [rval_g hg1] at h1
    obtain ⟨p, hp, hpt⟩ := hcov _ ((pt i).2 + gv g * (pt i).1) h1
    have hpe : (p.1, ((pt i).2 + gv g * (pt i).1) - gv g * p.1) = p := by
      ext
      · rfl
      · simp only; rw [← hpt]; ring
    have hm := mem_of_any _ _ (hx p.1)
    rw [hpe] at hm
    have h2 : ¬ rval S G (idx p) := hall _ (List.Mem.tail _ hm)
    rw [show rval S G (idx p) ↔ p ∈ S from by rw [rval_pt (idx_lt p), pt_idx]] at h2
    exact h2 hp
  · simp at h

theorem s_four (P : ZMod 35 × ZMod 35 → Prop) [DecidablePred P] (hP : (S.filter P).card ≤ 3)
    (c : List Sat.Literal) (h : chkFour P c = true) : (rval S G).satisfies c := by
  unfold chkFour at h
  split at h
  · rename_i i1 i2 i3 i4
    simp only [decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3, h4, hnd, p1, p2, p3, p4⟩ := h
    apply sat_of; intro hall
    have m1 : rval S G i1 := hall _ (List.Mem.head _)
    have m2 : rval S G i2 := hall _ (List.Mem.tail _ (List.Mem.head _))
    have m3 : rval S G i3 := hall _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have m4 : rval S G i4 := hall _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    rw [rval_pt h1] at m1
    rw [rval_pt h2] at m2
    rw [rval_pt h3] at m3
    rw [rval_pt h4] at m4
    have hsub : [pt i1, pt i2, pt i3, pt i4].toFinset ⊆ S.filter P := by
      intro p hp
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨m1, p1⟩
      · exact Finset.mem_filter.mpr ⟨m2, p2⟩
      · exact Finset.mem_filter.mpr ⟨m3, p3⟩
      · exact Finset.mem_filter.mpr ⟨m4, p4⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at this
    simp at this
    omega
  · simp at h

theorem s_width (hx : ∀ x : ZMod 35, (S.filter (fun p => p.1 = x)).card ≤ 3)
    (c : List Sat.Literal) (h : chkWidth c = true) : (rval S G).satisfies c := by
  unfold chkWidth at h
  split at h
  · rename_i i1 i2 i3 i4
    exact s_four S G _ (hx _) _ h
  · simp at h

theorem s_nb (hnb : ∀ a : ZMod 35, IsUnit a → a ∉ G →
      (G.filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5)
    (c : List Sat.Literal) (h : chkNb c = true) : (rval S G).satisfies c := by
  unfold chkNb at h
  split at h
  · rename_i ga b1 b2 b3 b4 b5 b6
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hga1, hga2, hb⟩, hnd, hrel⟩ := h
    apply sat_of; intro hall
    have h1 : ¬ rval S G ga := hall _ (List.Mem.head _)
    rw [rval_g hga1] at h1
    have hu : IsUnit (gv ga) := by
      obtain ⟨b, hb'⟩ := U_unit _ (gv_U hga1 hga2)
      exact IsUnit.of_mul_eq_one b hb'
    have hin : ∀ b ∈ [b1, b2, b3, b4, b5, b6], gv b ∈ G := by
      intro b hbm
      have hbm' : List.Mem (Sat.Literal.neg b)
          [.pos ga, .neg b1, .neg b2, .neg b3, .neg b4, .neg b5, .neg b6] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm
        rcases hbm with rfl | rfl | rfl | rfl | rfl | rfl <;>
          repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
      have := hall _ hbm'
      change rval S G b at this
      rwa [rval_g (hb b hbm).1] at this
    have hsub : [gv b1, gv b2, gv b3, gv b4, gv b5, gv b6].toFinset ⊆
        G.filter (fun b => b ≠ gv ga ∧ (b.val % 5 = (gv ga).val % 5 ∨ b.val % 7 = (gv ga).val % 7)) := by
      intro x hxm
      rw [List.mem_toFinset] at hxm
      have hr := hrel x hxm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm
      refine Finset.mem_filter.mpr ⟨?_, hr⟩
      rcases hxm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hin _ (by simp)
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at this
    have := hnb _ hu h1
    simp at *
    omega
  · simp at h

theorem s_count (h17 : 17 ≤ G.card) (hGU : G ⊆ U.toFinset)
    (c : List Sat.Literal) (h : chkCount c = true) : (rval S G).satisfies c := by
  unfold chkCount at h
  split at h
  · rename_i b1 b2 b3 b4 b5 b6 b7 b8
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, hnd⟩ := h
    apply sat_of; intro hall
    have hout : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], gv b ∉ G := by
      intro b hbm
      have hbm' : List.Mem (Sat.Literal.pos b)
          [.pos b1, .pos b2, .pos b3, .pos b4, .pos b5, .pos b6, .pos b7, .pos b8] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm
        rcases hbm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
      have := hall _ hbm'
      change ¬ rval S G b at this
      rwa [rval_g (hb b hbm).1] at this
    set L := [gv b1, gv b2, gv b3, gv b4, gv b5, gv b6, gv b7, gv b8] with hLdef
    have hLU : L.toFinset ⊆ U.toFinset := by
      intro x hxm
      rw [List.mem_toFinset] at hxm ⊢
      simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hxm
      rcases hxm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact gv_U (hb _ (by simp)).1 (hb _ (by simp)).2
    have hsub : G ⊆ U.toFinset \ L.toFinset := by
      intro x hx
      rw [Finset.mem_sdiff]
      refine ⟨hGU hx, fun hxL => ?_⟩
      rw [List.mem_toFinset] at hxL
      simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hxL
      rcases hxL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hout _ (by simp) hx
    have := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hLU, List.toFinset_card_of_nodup hnd, U_card] at this
    have hlen : L.length = 8 := by simp [hLdef]
    omega
  · simp at h

theorem s_hyp (Gin Gout : List (ZMod 35)) (hin : ∀ b ∈ Gin, b ∈ G) (hout : ∀ b ∈ Gout, b ∉ G)
    (c : List Sat.Literal) (h : chkHyp Gin Gout c = true) : (rval S G).satisfies c := by
  unfold chkHyp at h
  split at h
  · rename_i g
    simp only [decide_eq_true_eq] at h
    apply sat_of; intro hall
    have h1 : ¬ rval S G g := hall _ (List.Mem.head _)
    rw [rval_g h.1] at h1
    exact h1 (hin _ h.2)
  · rename_i g
    simp only [decide_eq_true_eq] at h
    apply sat_of; intro hall
    have h1 : rval S G g := hall _ (List.Mem.head _)
    rw [rval_g h.1] at h1
    exact hout _ h.2 h1
  · simp at h

theorem s_chk (A : ZMod 35 × ZMod 35) (Gin Gout : List (ZMod 35)) (hin : ∀ b ∈ Gin, b ∈ G) (hout : ∀ b ∈ Gout, b ∉ G) (h0 : (0, 0) ∈ S) (hA : A ∈ S)
    (hG : ∀ a, a ∈ G → Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S)
    (hcov : ∀ a t, a ∈ G → ∃ p ∈ S, p.2 + a * p.1 = t)
    (hx : ∀ x : ZMod 35, (S.filter (fun p => p.1 = x)).card ≤ 3)
    (hline : (S.filter (fun p => p.2 + p.1 = 0)).card ≤ 3)
    (hnb : ∀ a : ZMod 35, IsUnit a → a ∉ G →
      (G.filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5)
    (h17 : 17 ≤ G.card) (hGU : G ⊆ U.toFinset)
    (c : List Sat.Literal) (h : chk A Gin Gout c = true) : (rval S G).satisfies c := by
  unfold chk at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h)
  · exact s_anchor S G A h0 hA c h
  · exact s_amo S G hG c h
  · exact s_cover S G hcov c h
  · exact s_width S G hx c h
  · exact s_four S G _ hline c h
  · exact s_nb S G hnb c h
  · exact s_count S G h17 hGU c h
  · exact s_hyp S G Gin Gout hin hout c h

theorem s_fmla (A : ZMod 35 × ZMod 35) (Gin Gout : List (ZMod 35)) (hin : ∀ b ∈ Gin, b ∈ G) (hout : ∀ b ∈ Gout, b ∉ G) (h0 : (0, 0) ∈ S) (hA : A ∈ S)
    (hG : ∀ a, a ∈ G → Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S)
    (hcov : ∀ a t, a ∈ G → ∃ p ∈ S, p.2 + a * p.1 = t)
    (hx : ∀ x : ZMod 35, (S.filter (fun p => p.1 = x)).card ≤ 3)
    (hline : (S.filter (fun p => p.2 + p.1 = 0)).card ≤ 3)
    (hnb : ∀ a : ZMod 35, IsUnit a → a ∉ G →
      (G.filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5)
    (h17 : 17 ≤ G.card) (hGU : G ⊆ U.toFinset)
    (f : Sat.Fmla) (hf : f.all (chk A Gin Gout) = true) : (rval S G).satisfies_fmla f :=
  ⟨fun c hc => s_chk S G A Gin Gout hin hout h0 hA hG hcov hx hline hnb h17 hGU c
    (List.all_eq_true.mp hf c hc)⟩

end

end W35

theorem good_slopes_fiber35_sat_fmla_sound (S : Finset (ZMod 35 × ZMod 35)) (G : Finset (ZMod 35))
    (A : ZMod 35 × ZMod 35) (Gin Gout : List (ZMod 35)) (hin : ∀ b ∈ Gin, b ∈ G) (hout : ∀ b ∈ Gout, b ∉ G)
    (h0 : (0, 0) ∈ S) (hA : A ∈ S)
    (hG : ∀ a, a ∈ G → Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S)
    (hcov : ∀ a t, a ∈ G → ∃ p ∈ S, p.2 + a * p.1 = t)
    (hx : ∀ x : ZMod 35, (S.filter (fun p => p.1 = x)).card ≤ 3)
    (hline : (S.filter (fun p => p.2 + p.1 = 0)).card ≤ 3)
    (hnb : ∀ a : ZMod 35, IsUnit a → a ∉ G →
      (G.filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5)
    (h17 : 17 ≤ G.card) (hGU : G ⊆ W35.U.toFinset)
    (f : Sat.Fmla) (hf : f.all (W35.chk A Gin Gout) = true) : (W35.rval S G).satisfies_fmla f := by
  exact W35.s_fmla S G A Gin Gout hin hout h0 hA hG hcov hx hline hnb h17 hGU f hf
