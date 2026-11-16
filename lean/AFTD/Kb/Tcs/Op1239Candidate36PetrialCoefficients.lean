import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate36
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialNullityPolyCoeffEqPetrialCoeff
import AFTD.Kb.Tcs.Op1239Candidate36RecurrenceValues
import AFTD.Kb.Tcs.PetrialNullityPolyIso
import AFTD.Kb.Tcs.PetrialLeafOnePivot
import AFTD.Kb.Tcs.PetrialLeafRestrictionBijective
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList
import AFTD.Kb.Tcs.PetrialLeafFlipBijective
import AFTD.Kb.Tcs.PetrialLeafRestriction
import AFTD.Kb.Tcs.PetrialMatrix
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialLeafFlip
import AFTD.Kb.Tcs.PetrialLeafZeroPivot
import AFTD.Kb.Tcs.G

/-!
# op_1239_candidate36_petrial_coefficients

Topic: combinatorics   Node: 2de8180bbaf9

Provenance: helper lemma. Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

The partial Petrial coefficients of op_1239_candidate36 in ranks 27, 28, and 29 are respectively 256, 32640, and 4666944.
-/

namespace Op1239C36Cert

theorem card_compl_one {V : Type*} [Fintype V] [DecidableEq V] (v : V) [Fintype ↥({v}ᶜ : Set V)] :
    Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := by
  classical
  rw [← Set.toFinset_card]
  simp [Set.toFinset_compl, Finset.card_compl]

theorem card_compl_two {V : Type*} [Fintype V] [DecidableEq V] (u v : V) (h : u ≠ v)
    [Fintype ↥({u, v}ᶜ : Set V)] :
    Fintype.card ↥({u, v}ᶜ : Set V) = Fintype.card V - 2 := by
  classical
  rw [← Set.toFinset_card]
  simp [Set.toFinset_compl, Finset.card_compl, Set.toFinset_insert, h]
  omega

theorem leaf_rec' {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v u : V}
    (hu : T.Adj v u) (huniq : ∀ w, T.Adj v w → w = u) :
    petrial_nullity_poly T
      = petrial_nullity_poly (T.induce ({v}ᶜ : Set V))
        + 2 * petrial_nullity_poly (T.induce ({u, v}ᶜ : Set V)) := by
  classical
  have hvu : v ≠ u := T.ne_of_adj hu
  unfold petrial_nullity_poly
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun F : Finset V => v ∈ F)]
  congr 1
  · rw [Finset.sum_subtype (Finset.univ.filter (fun F : Finset V => v ∈ F))
      (p := fun F : Finset V => v ∈ F) (by simp)]
    have hc := card_compl_one v (V := V)
    have key : ∀ F : {F : Finset V // v ∈ F},
        (Polynomial.X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank)
          = (fun S => (Polynomial.X : Polynomial ℕ) ^ (Fintype.card ↥({v}ᶜ : Set V) -
              (petrial_matrix (T.induce ({v}ᶜ : Set V)) S).rank)) (petrial_leaf_flip v u F.1) := by
      intro F
      simp only
      rw [petrial_leaf_one_pivot T v u F.1 F.2 hu huniq, hc, Nat.sub_add_eq]
    rw [Fintype.sum_congr _ _ key]
    exact (petrial_leaf_flip_bijective v u (Ne.symm hvu)).sum_comp
      (fun S => (Polynomial.X : Polynomial ℕ) ^ (Fintype.card ↥({v}ᶜ : Set V) -
              (petrial_matrix (T.induce ({v}ᶜ : Set V)) S).rank))
  · rw [Finset.sum_subtype (Finset.univ.filter (fun F : Finset V => ¬ v ∈ F))
      (p := fun F : Finset V => ¬ v ∈ F) (by simp)]
    have hc := card_compl_two u v (Ne.symm hvu) (V := V)
    let g : Finset ↥({u, v}ᶜ : Set V) → Polynomial ℕ := fun S =>
      (Polynomial.X : Polynomial ℕ) ^ (Fintype.card ↥({u, v}ᶜ : Set V) -
              (petrial_matrix (T.induce ({u, v}ᶜ : Set V)) S).rank)
    have key : ∀ F : {F : Finset V // ¬ v ∈ F},
        (Polynomial.X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank)
          = (fun p : Bool × Finset ↥({u, v}ᶜ : Set V) => g p.2)
              (decide (u ∈ F.1), petrial_leaf_restriction v u F.1) := by
      intro F
      simp only [g]
      rw [petrial_leaf_zero_pivot T v u F.1 F.2 hu huniq, hc, Nat.sub_add_eq]
    rw [Fintype.sum_congr _ _ key]
    rw [(petrial_leaf_restriction_bijective v u hvu).sum_comp
      (fun p : Bool × Finset ↥({u, v}ᶜ : Set V) => g p.2)]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, two_mul]
    rfl

theorem kerBlock {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (D : Matrix n n K) :
    Module.finrank K (LinearMap.ker (Matrix.fromBlocks A 0 0 D).mulVecLin) =
      Module.finrank K (LinearMap.ker A.mulVecLin) + Module.finrank K (LinearMap.ker D.mulVecLin) := by
  let e : LinearMap.ker (Matrix.fromBlocks A 0 0 D).mulVecLin ≃ₗ[K]
      (LinearMap.ker A.mulVecLin) × (LinearMap.ker D.mulVecLin) := {
    toFun := fun x => (⟨fun i => x.1 (Sum.inl i), by
        have hx := x.2
        change Matrix.mulVec (Matrix.fromBlocks A 0 0 D) x.1 = 0 at hx
        change A.mulVec (fun i => x.1 (Sum.inl i)) = 0
        funext i
        have hi := congrFun hx (Sum.inl i)
        simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using hi⟩,
      ⟨fun i => x.1 (Sum.inr i), by
        have hx := x.2
        change Matrix.mulVec (Matrix.fromBlocks A 0 0 D) x.1 = 0 at hx
        change D.mulVec (fun i => x.1 (Sum.inr i)) = 0
        funext i
        have hi := congrFun hx (Sum.inr i)
        simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using hi⟩)
    invFun := fun y => ⟨Sum.elim y.1.1 y.2.1, by
      have h1 := y.1.2
      have h2 := y.2.2
      change A.mulVec y.1.1 = 0 at h1
      change D.mulVec y.2.1 = 0 at h2
      change Matrix.mulVec (Matrix.fromBlocks A 0 0 D) (Sum.elim y.1.1 y.2.1) = 0
      funext i
      cases i with
      | inl i =>
        have hi := congrFun h1 i
        simpa [Matrix.fromBlocks_mulVec] using hi
      | inr i =>
        have hi := congrFun h2 i
        simpa [Matrix.fromBlocks_mulVec] using hi⟩
    left_inv := fun x => by
      apply Subtype.ext
      funext i
      cases i <;> rfl
    right_inv := fun y => rfl
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl
  }
  rw [e.finrank_eq, Module.finrank_prod]

theorem rank_blockdiag {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (D : Matrix n n K) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  have he := kerBlock A D
  have h₁ := (Matrix.fromBlocks A 0 0 D).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.mulVecLin.finrank_range_add_finrank_ker
  have h₃ := D.mulVecLin.finrank_range_add_finrank_ker
  change (Matrix.fromBlocks A 0 0 D).rank + _ = _ at h₁
  change A.rank + _ = _ at h₂
  change D.rank + _ = _ at h₃
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h₁ h₂ h₃
  omega

theorem mul_of_cut' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) [DecidablePred (· ∈ s)]
    (hcut : ∀ a b : V, a ∈ s → b ∉ s → ¬ G.Adj a b) :
    petrial_nullity_poly G
      = petrial_nullity_poly (G.induce s) * petrial_nullity_poly (G.induce sᶜ) := by
  classical
  unfold petrial_nullity_poly
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  let φ : Finset V → Finset s × Finset ↥sᶜ := fun F =>
    (Finset.univ.filter (fun x : s => x.1 ∈ F), Finset.univ.filter (fun x : ↥sᶜ => x.1 ∈ F))
  have hφ : Function.Bijective φ := by
    constructor
    · intro F F' h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      ext x
      by_cases hx : x ∈ s
      · have := congrArg (fun S => (⟨x, hx⟩ : s) ∈ S) h1
        simpa [φ] using this
      · have := congrArg (fun S => (⟨x, hx⟩ : ↥sᶜ) ∈ S) h2
        simpa [φ] using this
    · rintro ⟨A, B⟩
      refine ⟨A.map (Function.Embedding.subtype _) ∪ B.map (Function.Embedding.subtype _), ?_⟩
      apply Prod.ext
      · ext x
        simp only [φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Finset.mem_map, Function.Embedding.coe_subtype]
        constructor
        · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
          · have : y = x := Subtype.ext he
            simpa [this] using hy
          · exact absurd (he ▸ x.2) y.2
        · intro hx; exact Or.inl ⟨x, hx, rfl⟩
      · ext x
        simp only [φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Finset.mem_map, Function.Embedding.coe_subtype]
        constructor
        · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
          · exact absurd (he ▸ y.2) x.2
          · have : y = x := Subtype.ext he
            simpa [this] using hy
        · intro hx; exact Or.inr ⟨x, hx, rfl⟩
  have hprod : (Finset.univ : Finset (Finset s × Finset ↥sᶜ)) = Finset.univ ×ˢ Finset.univ := rfl
  rw [← hprod]
  rw [← hφ.sum_comp]
  apply Fintype.sum_congr
  intro F
  rw [← pow_add]
  congr 1
  let e := Equiv.Set.sumCompl s
  have hM : (petrial_matrix G F).submatrix e e =
      Matrix.fromBlocks (petrial_matrix (G.induce s) (φ F).1) 0 0
        (petrial_matrix (G.induce sᶜ) (φ F).2) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [e, φ, petrial_matrix, Matrix.diagonal_apply, Subtype.ext_iff]
    · have hij : (i : V) ≠ j := fun h => j.2 (h ▸ i.2)
      have hadj := hcut i j i.2 j.2
      simp [e, petrial_matrix, Matrix.diagonal_apply, hij, hadj]
    · have hij : (i : V) ≠ j := fun h => i.2 (h ▸ j.2)
      have hadj : ¬ G.Adj i j := fun h => hcut j i j.2 i.2 h.symm
      simp [e, petrial_matrix, Matrix.diagonal_apply, hij, hadj]
    · simp [e, φ, petrial_matrix, Matrix.diagonal_apply, Subtype.ext_iff]
  have hr : (petrial_matrix G F).rank = (petrial_matrix (G.induce s) (φ F).1).rank +
      (petrial_matrix (G.induce sᶜ) (φ F).2).rank := by
    rw [← rank_blockdiag, ← hM, Matrix.rank_submatrix]
  have hc : Fintype.card V = Fintype.card s + Fintype.card ↥sᶜ := by
    rw [← Fintype.card_sum]; exact (Fintype.card_congr e).symm
  have h1 := (petrial_matrix (G.induce s) (φ F).1).rank_le_card_width
  have h2 := (petrial_matrix (G.induce sᶜ) (φ F).2).rank_le_card_width
  rw [hr, hc]
  omega


def isoOfMem {V : Type*} (G : SimpleGraph V) {s t : Set V} (A : Set s)
    (h : ∀ x, x ∈ t ↔ ∃ hx : x ∈ s, (⟨x, hx⟩ : s) ∈ A) : (G.induce s).induce A ≃g G.induce t where
  toFun a := ⟨a.1.1, (h _).2 ⟨a.1.2, a.2⟩⟩
  invFun b := ⟨⟨b.1, ((h _).1 b.2).1⟩, ((h _).1 b.2).2⟩
  left_inv a := rfl
  right_inv b := rfl
  map_rel_iff' := Iff.rfl

def isoOfEq {V : Type*} (G : SimpleGraph V) {s t : Set V} (h : s = t) : G.induce s ≃g G.induce t where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl

noncomputable def pl : List ℕ → Polynomial ℕ
  | [] => 0
  | a :: l => Polynomial.C a + Polynomial.X * pl l

def padd : List ℕ → List ℕ → List ℕ
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::padd as bs

def pmul : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a::as, b => padd (b.map (a * ·)) (0 :: pmul as b)

theorem pl_padd : ∀ a b : List ℕ, pl (padd a b) = pl a + pl b
  | [], b => by simp [padd, pl]
  | a :: as, [] => by simp [padd, pl]
  | a :: as, b :: bs => by
    simp only [padd, pl, pl_padd as bs, map_add]
    ring

theorem pl_map (c : ℕ) : ∀ b : List ℕ, pl (b.map (c * ·)) = Polynomial.C c * pl b
  | [] => by simp [pl]
  | a :: as => by
    simp only [List.map_cons, pl, pl_map c as, map_mul]
    ring

theorem pl_pmul : ∀ a b : List ℕ, pl (pmul a b) = pl a * pl b
  | [], b => by simp [pmul, pl]
  | a :: as, b => by
    simp only [pmul, pl_padd, pl_map, pl, pl_pmul as b, map_zero]
    ring

theorem pl_leaf (A B C : List ℕ) (h : padd A (B.map (2 * ·)) = C) : pl A + 2 * pl B = pl C := by
  rw [← h, pl_padd, pl_map]
  simp

theorem pl_mul (A B C : List ℕ) (h : pmul A B = C) : pl A * pl B = pl C := by
  rw [← h, pl_pmul]

theorem pl_coeff : ∀ (l : List ℕ) (n : ℕ), (pl l).coeff n = l.getD n 0
  | [], n => by simp [pl]
  | a :: l, 0 => by simp [pl]
  | a :: l, n + 1 => by
    simp [pl, Polynomial.coeff_C, pl_coeff l n]

theorem P_card_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (H : SimpleGraph ι) [DecidableRel H.Adj]
    (hc : Fintype.card ι = 0) : petrial_nullity_poly H = pl [1] := by
  unfold petrial_nullity_poly
  have : ∀ F : Finset ι, F = ∅ := by
    intro F; ext x; exact ((Fintype.card_eq_zero_iff.mp hc).false x).elim
  rw [Fintype.sum_eq_single ∅ (fun F hF => absurd (this F) hF)]
  simp [hc, pl]

theorem P_card_one {ι : Type*} [Fintype ι] [DecidableEq ι] (H : SimpleGraph ι) [DecidableRel H.Adj]
    (hc : Fintype.card ι = 1) : petrial_nullity_poly H = pl [1, 1] := by
  unfold petrial_nullity_poly
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hc
  have huniv : (Finset.univ : Finset (Finset ι)) = {∅, {x}} := by
    ext F
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hxF : x ∈ F
    · right; ext y; rw [hx y]; simp [hxF]
    · left; ext y; rw [hx y]; simp [hxF]
  rw [huniv, Finset.sum_pair (Finset.singleton_ne_empty x).symm]
  have h0 : petrial_matrix H ∅ = 0 := by
    ext i j
    rw [hx i, hx j]
    simp [petrial_matrix]
  have h1 : petrial_matrix H {x} = 1 := by
    ext i j
    rw [hx i, hx j]
    simp [petrial_matrix]
  rw [h0, h1, Matrix.rank_zero, Matrix.rank_one, hc]
  simp [pl]
  ring

def mset {n : ℕ} (m : ℕ) : Set (Fin n) := {x | m.testBit x.val = true}

local instance {n : ℕ} (m : ℕ) : DecidablePred (· ∈ (mset m : Set (Fin n))) :=
  fun x => inferInstanceAs (Decidable (m.testBit x.val = true))

noncomputable def Qm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) : Polynomial ℕ :=
  petrial_nullity_poly (G.induce (mset m))

theorem testBit_xor_pow (m k i : ℕ) : (m ^^^ 2 ^ k).testBit i = (m.testBit i ^^ decide (k = i)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem leafM {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (nb : Fin n → ℕ)
    (hnb : ∀ a b, G.Adj a b ↔ (nb a).testBit b.val = true) (m m1 m2 : ℕ) (v u : Fin n)
    (h : (m.testBit v.val && m.testBit u.val && (nb v &&& m == 2 ^ u.val) &&
      (m1 == m ^^^ 2 ^ v.val) && (m2 == m1 ^^^ 2 ^ u.val)) = true) :
    Qm G m = Qm G m1 + 2 * Qm G m2 := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hv, hu⟩, hnbm⟩, h1⟩, h2⟩ := h
  have hvu : (nb v).testBit u.val = true := by
    have := congrArg (fun t => t.testBit u.val) hnbm
    simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.and_eq_true] at this
    exact this.1
  have hA' : G.Adj v u := (hnb v u).2 hvu
  have huv : u ≠ v := (G.ne_of_adj hA').symm
  have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
  unfold Qm
  have hv' : v ∈ (mset m : Set (Fin n)) := hv
  have hu' : u ∈ (mset m : Set (Fin n)) := hu
  have hA : (G.induce (mset m)).Adj ⟨v, hv'⟩ ⟨u, hu'⟩ := hA'
  have hU : ∀ w, (G.induce (mset m)).Adj ⟨v, hv'⟩ w → w = ⟨u, hu'⟩ := by
    intro w hw
    apply Subtype.ext
    have hb : (nb v).testBit w.1.val = true := (hnb _ _).1 hw
    have hwm : m.testBit w.1.val = true := w.2
    have := congrArg (fun t => t.testBit w.1.val) hnbm
    simp only [Nat.testBit_and, hb, hwm, Bool.and_self, Nat.testBit_two_pow] at this
    have h' : u.val = w.1.val := by simpa using this
    exact Fin.ext h'.symm
  have key1 : ∀ y : (mset m : Set (Fin n)), y ∈ ({⟨v, hv'⟩}ᶜ : Set (mset m : Set (Fin n))) ↔ y.1 ≠ v := by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun h e => h (Subtype.ext e), fun h e => h (congrArg Subtype.val e)⟩
  have key2 : ∀ y : (mset m : Set (Fin n)),
      y ∈ ({⟨u, hu'⟩, ⟨v, hv'⟩}ᶜ : Set (mset m : Set (Fin n))) ↔ (y.1 ≠ u ∧ y.1 ≠ v) := by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun e => h1 (Subtype.ext e), fun e => h2 (Subtype.ext e)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e)⟩
  have e1 : petrial_nullity_poly ((G.induce (mset m)).induce ({⟨v, hv'⟩}ᶜ : Set _)) =
      petrial_nullity_poly (G.induce (mset m1 : Set (Fin n))) := by
    apply petrial_nullity_poly_iso
    apply isoOfMem
    intro x
    simp only [key1]
    subst h1
    show (m ^^^ 2 ^ v.val).testBit x.val = true ↔ ∃ _ : m.testBit x.val = true, x ≠ v
    rw [testBit_xor_pow]
    by_cases hx : x = v
    · subst hx; simp [hv]
    · have hx' : v.val ≠ x.val := fun h => hx (Fin.ext h.symm)
      simp [hx, hx']
  have e2 : petrial_nullity_poly ((G.induce (mset m)).induce ({⟨u, hu'⟩, ⟨v, hv'⟩}ᶜ : Set _)) =
      petrial_nullity_poly (G.induce (mset m2 : Set (Fin n))) := by
    apply petrial_nullity_poly_iso
    apply isoOfMem
    intro x
    simp only [key2]
    subst h1 h2
    show (m ^^^ 2 ^ v.val ^^^ 2 ^ u.val).testBit x.val = true ↔
      ∃ _ : m.testBit x.val = true, (x ≠ u ∧ x ≠ v)
    rw [testBit_xor_pow, testBit_xor_pow]
    by_cases hx : x = v
    · subst hx; simp [hv, huv']
    · by_cases hxu : x = u
      · subst hxu; simp [hu, huv', Ne.symm huv']
      · have hx' : v.val ≠ x.val := fun h => hx (Fin.ext h.symm)
        have hxu' : u.val ≠ x.val := fun h => hxu (Fin.ext h.symm)
        simp [hx, hx', hxu, hxu']
  rw [leaf_rec' _ hA hU, e1, e2]

def cutB {n : ℕ} (nb : Fin n → ℕ) (a b : ℕ) : Bool :=
  (List.finRange n).all (fun x => !a.testBit x.val || (nb x &&& b == 0))

theorem cutM {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (nb : Fin n → ℕ)
    (hnb : ∀ a b, G.Adj a b ↔ (nb a).testBit b.val = true) (m a b : ℕ)
    (h : ((m == a ||| b) && (a &&& b == 0) && cutB nb a b) = true) :
    Qm G m = Qm G a * Qm G b := by
  classical
  simp only [Bool.and_eq_true, beq_iff_eq, cutB, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hm, hab⟩, hc⟩ := h
  have hmx : ∀ x : ℕ, m.testBit x = (a.testBit x || b.testBit x) := by
    intro x; rw [hm, Nat.testBit_or]
  have habx : ∀ x : ℕ, a.testBit x = true → b.testBit x = false := by
    intro x hx
    have := congrArg (fun t => t.testBit x) hab
    simp only [Nat.testBit_and, hx, Bool.true_and, Nat.zero_testBit] at this
    exact this
  unfold Qm
  rw [mul_of_cut' (G.induce (mset m)) {x | a.testBit x.1.val = true}]
  · congr 1
    · apply petrial_nullity_poly_iso
      apply isoOfMem
      intro x
      simp only [mset, Set.mem_setOf_eq, hmx, Bool.or_eq_true]
      constructor
      · intro hx; exact ⟨Or.inl hx, hx⟩
      · intro hx; exact hx.2
    · apply petrial_nullity_poly_iso
      apply isoOfMem
      intro x
      simp only [mset, Set.mem_setOf_eq, Set.mem_compl_iff, hmx, Bool.or_eq_true]
      constructor
      · intro hx
        refine ⟨Or.inr hx, ?_⟩
        intro hxa
        have := habx _ hxa
        rw [hx] at this
        exact absurd this (by decide)
      · rintro ⟨hxl, hxa⟩
        rcases hxl with h | h
        · exact absurd h hxa
        · exact h
  · intro x y hx hy hxy
    have hym : m.testBit y.1.val = true := y.2
    have hyb : b.testBit y.1.val = true := by
      rw [hmx] at hym
      rcases Bool.or_eq_true_iff.mp hym with h | h
      · exact absurd h hy
      · exact h
    have h4 : (nb x.1).testBit y.1.val = true := (hnb x.1 y.1).1 hxy
    rcases hc x.1 with h | h
    · rw [hx] at h; exact absurd h (by decide)
    · have := congrArg (fun t => t.testBit y.1.val) h
      simp only [Nat.testBit_and, h4, hyb, Bool.and_self, Nat.zero_testBit] at this
      exact absurd this (by decide)

theorem Qm_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Qm G 0 = pl [1] := by
  unfold Qm
  apply P_card_zero
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro x
  have := x.2
  simp [mset] at this

theorem Qm_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Qm G (2 ^ v.val) = pl [1, 1] := by
  unfold Qm
  apply P_card_one
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨v, by simp [mset, Nat.testBit_two_pow]⟩, fun y => ?_⟩
  apply Subtype.ext
  have := y.2
  simp only [mset, Set.mem_setOf_eq, Nat.testBit_two_pow, decide_eq_true_eq] at this
  exact Fin.ext this.symm

def nbOf {n : ℕ} (L : List (Fin n × Fin n)) (a : Fin n) : ℕ :=
  L.foldr (fun p acc => ((if p.1 = a then 2 ^ p.2.val else 0) ||| (if p.2 = a then 2 ^ p.1.val else 0)) ||| acc) 0

theorem testBit_ite_pow (c : Prop) [Decidable c] (k i : ℕ) :
    (if c then 2 ^ k else 0).testBit i = (decide c && decide (k = i)) := by
  by_cases hc : c <;> simp [hc, Nat.testBit_two_pow]

theorem testBit_nbOf {n : ℕ} (L : List (Fin n × Fin n)) (a b : Fin n) :
    (nbOf L a).testBit b.val = true ↔ ((a, b) ∈ L ∨ (b, a) ∈ L) := by
  induction L with
  | nil => simp [nbOf]
  | cons p L ih =>
    obtain ⟨p1, p2⟩ := p
    have e : nbOf ((p1, p2) :: L) a = ((if p1 = a then 2 ^ p2.val else 0) |||
        (if p2 = a then 2 ^ p1.val else 0)) ||| nbOf L a := rfl
    rw [e, Nat.testBit_or, Nat.testBit_or, testBit_ite_pow, testBit_ite_pow]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih, List.mem_cons,
      Prod.mk.injEq, Fin.val_inj]
    constructor
    · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (h | h)) <;> simp [*]
    · rintro ((⟨rfl, rfl⟩ | h) | (⟨rfl, rfl⟩ | h)) <;> simp [*]

theorem hnb_of_list {n : ℕ} (L : List (Fin n × Fin n))
    (hloop : L.all (fun p => p.1 != p.2) = true) :
    ∀ a b, (simple_graph_of_edge_list L).Adj a b ↔ (nbOf L a).testBit b.val = true := by
  intro a b
  rw [testBit_nbOf]
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at hloop
  simp only [simple_graph_of_edge_list, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with h | h
    · exact hloop _ h
    · exact fun e => hloop _ h e.symm

theorem Qm_single' {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) (v : Fin n)
    (h : m = 2 ^ v.val) : Qm G m = pl [1, 1] := by
  rw [h]; exact Qm_single G v

def L36 : List (Fin 36 × Fin 36) := [(0, 1), (0, 3), (0, 8), (1, 2), (1, 4), (2, 6), (2, 7), (3, 5), (3, 21), (4, 12), (4, 16), (5, 13), (5, 14), (6, 9), (6, 18), (7, 10), (7, 15), (8, 11), (8, 26), (10, 19), (10, 30), (11, 27), (11, 33), (12, 22), (13, 17), (14, 24), (16, 20), (16, 31), (18, 29), (18, 32), (20, 23), (20, 28), (23, 25), (28, 34), (29, 35)]

def nb36 : Fin 36 → ℕ := nbOf L36

theorem hnb36 : ∀ a b, op_1239_candidate36.Adj a b ↔ (nb36 a).testBit b.val = true :=
  hnb_of_list L36 (by decide)

section
variable [DecidableRel op_1239_candidate36.Adj]

theorem c36q0 : Qm op_1239_candidate36 34896609280 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896609280 34359738368 0 29 35 rfl, (Qm_single' op_1239_candidate36 34359738368 35 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q1 : Qm op_1239_candidate36 34896871424 = pl [5, 3] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896871424 34896609280 34359738368 18 29 rfl, c36q0, (Qm_single' op_1239_candidate36 34359738368 35 rfl)]
  exact pl_leaf _ _ _ rfl

theorem c36q2 : Qm op_1239_candidate36 34896871488 = pl [11, 5] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896871488 34896871424 34896609280 6 18 rfl, c36q1, c36q0]
  exact pl_leaf _ _ _ rfl

theorem c36q3 : Qm op_1239_candidate36 34896871492 = pl [21, 11] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896871492 34896871488 34896871424 2 6 rfl, c36q2, c36q1]
  exact pl_leaf _ _ _ rfl

theorem c36q4 : Qm op_1239_candidate36 34896871494 = pl [43, 21] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896871494 34896871492 34896871488 1 2 rfl, c36q3, c36q2]
  exact pl_leaf _ _ _ rfl

theorem c36q5 : Qm op_1239_candidate36 34896871510 = pl [85, 43] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896871510 34896871494 34896871492 4 1 rfl, c36q4, c36q3]
  exact pl_leaf _ _ _ rfl

theorem c36q6 : Qm op_1239_candidate36 34896937046 = pl [171, 85] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34896937046 34896871510 34896871494 16 4 rfl, c36q5, c36q4]
  exact pl_leaf _ _ _ rfl

theorem c36q7 : Qm op_1239_candidate36 34897985622 = pl [341, 171] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 34897985622 34896937046 34896871510 20 16 rfl, c36q6, c36q5]
  exact pl_leaf _ _ _ rfl

theorem c36q8 : Qm op_1239_candidate36 35166421078 = pl [683, 341] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 35166421078 34897985622 34896937046 28 20 rfl, c36q7, c36q6]
  exact pl_leaf _ _ _ rfl

theorem c36q9 : Qm op_1239_candidate36 52346290262 = pl [1365, 683] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 52346290262 35166421078 34897985622 34 28 rfl, c36q8, c36q7]
  exact pl_leaf _ _ _ rfl

theorem c36q10 : Qm op_1239_candidate36 17448304640 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17448304640 17179869184 0 28 34 rfl, (Qm_single' op_1239_candidate36 17179869184 34 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q11 : Qm op_1239_candidate36 52345241686 = pl [513, 426, 85] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 52345241686 34896937046 17448304640 rfl, c36q6, c36q10]
  exact pl_mul _ _ _ rfl

theorem c36q12 : Qm op_1239_candidate36 52354678870 = pl [2391, 1535, 170] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 52354678870 52346290262 52345241686 23 20 rfl, c36q9, c36q11]
  exact pl_leaf _ _ _ rfl

theorem c36q13 : Qm op_1239_candidate36 52388233302 = pl [5121, 2901, 170] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 52388233302 52354678870 52346290262 25 23 rfl, c36q12, c36q9]
  exact pl_leaf _ _ _ rfl

theorem c36q14 : Qm op_1239_candidate36 17449353216 = pl [5, 3] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17449353216 17448304640 17179869184 20 28 rfl, c36q10, (Qm_single' op_1239_candidate36 17179869184 34 rfl)]
  exact pl_leaf _ _ _ rfl

theorem c36q15 : Qm op_1239_candidate36 17457741824 = pl [11, 5] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17457741824 17449353216 17448304640 23 20 rfl, c36q14, c36q10]
  exact pl_leaf _ _ _ rfl

theorem c36q16 : Qm op_1239_candidate36 17491296256 = pl [21, 11] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491296256 17457741824 17449353216 25 23 rfl, c36q15, c36q14]
  exact pl_leaf _ _ _ rfl

theorem c36q17 : Qm op_1239_candidate36 41943040 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 41943040 33554432 0 23 25 rfl, (Qm_single' op_1239_candidate36 33554432 25 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q18 : Qm op_1239_candidate36 17490247680 = pl [9, 6, 1] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 17490247680 41943040 17448304640 rfl, c36q17, c36q10]
  exact pl_mul _ _ _ rfl

theorem c36q19 : Qm op_1239_candidate36 17491361792 = pl [39, 23, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491361792 17491296256 17490247680 16 20 rfl, c36q16, c36q18]
  exact pl_leaf _ _ _ rfl

theorem c36q20 : Qm op_1239_candidate36 17491361808 = pl [81, 45, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491361808 17491361792 17491296256 4 16 rfl, c36q19, c36q16]
  exact pl_leaf _ _ _ rfl

theorem c36q21 : Qm op_1239_candidate36 17491361810 = pl [159, 91, 6] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491361810 17491361808 17491361792 1 4 rfl, c36q20, c36q19]
  exact pl_leaf _ _ _ rfl

theorem c36q22 : Qm op_1239_candidate36 17491361814 = pl [321, 181, 10] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491361814 17491361810 17491361808 2 1 rfl, c36q21, c36q20]
  exact pl_leaf _ _ _ rfl

theorem c36q23 : Qm op_1239_candidate36 17491361878 = pl [639, 363, 22] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491361878 17491361814 17491361810 6 2 rfl, c36q22, c36q21]
  exact pl_leaf _ _ _ rfl

theorem c36q24 : Qm op_1239_candidate36 52387971158 = pl [1917, 1728, 429, 22] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 52387971158 17491361878 34896609280 rfl, c36q23, c36q0]
  exact pl_mul _ _ _ rfl

theorem c36q25 : Qm op_1239_candidate36 56683200598 = pl [8955, 6357, 1028, 44] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 56683200598 52388233302 52387971158 32 18 rfl, c36q13, c36q24]
  exact pl_leaf _ _ _ rfl

theorem c36q26 : Qm op_1239_candidate36 39191838720 = pl [11, 5] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838720 34896871424 34896609280 32 18 rfl, c36q1, c36q0]
  exact pl_leaf _ _ _ rfl

theorem c36q27 : Qm op_1239_candidate36 39191576576 = pl [3, 4, 1] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 39191576576 34896609280 4294967296 rfl, c36q0, (Qm_single' op_1239_candidate36 4294967296 32 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q28 : Qm op_1239_candidate36 39191838784 = pl [17, 13, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838784 39191838720 39191576576 6 18 rfl, c36q26, c36q27]
  exact pl_leaf _ _ _ rfl

theorem c36q29 : Qm op_1239_candidate36 56683200594 = pl [2703, 3614, 1603, 260, 12] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 56683200594 17491361810 39191838784 rfl, c36q21, c36q28]
  exact pl_mul _ _ _ rfl

theorem c36q30 : Qm op_1239_candidate36 56683200726 = pl [14361, 13585, 4234, 564, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 56683200726 56683200598 56683200594 7 2 rfl, c36q25, c36q29]
  exact pl_leaf _ _ _ rfl

theorem c36q31 : Qm op_1239_candidate36 56683201750 = pl [32271, 26299, 6290, 652, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 56683201750 56683200726 56683200598 10 7 rfl, c36q30, c36q25]
  exact pl_leaf _ _ _ rfl

theorem c36q32 : Qm op_1239_candidate36 57756943574 = pl [60993, 53469, 14758, 1780, 72] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 57756943574 56683201750 56683200726 30 10 rfl, c36q31, c36q30]
  exact pl_leaf _ _ _ rfl

theorem c36q33 : Qm op_1239_candidate36 57756942550 = pl [14361, 27946, 17819, 4798, 588, 24] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 57756942550 56683200726 1073741824 rfl, c36q30, (Qm_single' op_1239_candidate36 1073741824 30 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q34 : Qm op_1239_candidate36 57757467862 = pl [89715, 109361, 50396, 11376, 1248, 48] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 57757467862 57756943574 57756942550 19 10 rfl, c36q32, c36q33]
  exact pl_leaf _ _ _ rfl

theorem c36q35 : Qm op_1239_candidate36 39191838788 = pl [39, 23, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838788 39191838784 39191838720 2 6 rfl, c36q28, c36q26]
  exact pl_leaf _ _ _ rfl

theorem c36q36 : Qm op_1239_candidate36 39191838916 = pl [73, 49, 6] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838916 39191838788 39191838784 7 2 rfl, c36q35, c36q28]
  exact pl_leaf _ _ _ rfl

theorem c36q37 : Qm op_1239_candidate36 39191839940 = pl [151, 95, 10] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191839940 39191838916 39191838788 10 7 rfl, c36q36, c36q35]
  exact pl_leaf _ _ _ rfl

theorem c36q38 : Qm op_1239_candidate36 40265581764 = pl [297, 193, 22] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40265581764 39191839940 39191838916 30 10 rfl, c36q37, c36q36]
  exact pl_leaf _ _ _ rfl

theorem c36q39 : Qm op_1239_candidate36 40265580740 = pl [73, 122, 55, 6] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 40265580740 39191838916 1073741824 rfl, c36q36, (Qm_single' op_1239_candidate36 1073741824 30 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q40 : Qm op_1239_candidate36 40266106052 = pl [443, 437, 132, 12] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266106052 40265581764 40265580740 19 10 rfl, c36q38, c36q39]
  exact pl_leaf _ _ _ rfl

theorem c36q41 : Qm op_1239_candidate36 1073742848 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1073742848 1073741824 0 10 30 rfl, (Qm_single' op_1239_candidate36 1073741824 30 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q42 : Qm op_1239_candidate36 1074267136 = pl [5, 3] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267136 1073742848 1073741824 19 10 rfl, c36q41, (Qm_single' op_1239_candidate36 1073741824 30 rfl)]
  exact pl_leaf _ _ _ rfl

theorem c36q43 : Qm op_1239_candidate36 1074266112 = pl [1, 2, 1] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 1074266112 524288 1073741824 rfl, (Qm_single' op_1239_candidate36 524288 19 rfl), (Qm_single' op_1239_candidate36 1073741824 30 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q44 : Qm op_1239_candidate36 1074267264 = pl [7, 7, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267264 1074267136 1074266112 7 10 rfl, c36q42, c36q43]
  exact pl_leaf _ _ _ rfl

theorem c36q45 : Qm op_1239_candidate36 40266106048 = pl [119, 210, 139, 40, 4] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 40266106048 39191838784 1074267264 rfl, c36q28, c36q44]
  exact pl_mul _ _ _ rfl

theorem c36q46 : Qm op_1239_candidate36 40266106054 = pl [681, 857, 410, 92, 8] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266106054 40266106052 40266106048 1 2 rfl, c36q40, c36q45]
  exact pl_leaf _ _ _ rfl

theorem c36q47 : Qm op_1239_candidate36 40266106070 = pl [1567, 1731, 674, 116, 8] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266106070 40266106054 40266106052 4 1 rfl, c36q46, c36q40]
  exact pl_leaf _ _ _ rfl

theorem c36q48 : Qm op_1239_candidate36 57757402326 = pl [32907, 53588, 33195, 9850, 1444, 88] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 57757402326 40266106070 17491296256 rfl, c36q47, c36q16]
  exact pl_mul _ _ _ rfl

theorem c36q49 : Qm op_1239_candidate36 59904951510 = pl [155529, 216537, 116786, 31076, 4136, 224] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59904951510 57757467862 57757402326 31 16 rfl, c36q34, c36q48]
  exact pl_leaf _ _ _ rfl

theorem c36q50 : Qm op_1239_candidate36 19638845440 = pl [81, 45, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638845440 17491361792 17491296256 31 16 rfl, c36q19, c36q16]
  exact pl_leaf _ _ _ rfl

theorem c36q51 : Qm op_1239_candidate36 19638779904 = pl [21, 32, 11] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 19638779904 17491296256 2147483648 rfl, c36q16, (Qm_single' op_1239_candidate36 2147483648 31 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q52 : Qm op_1239_candidate36 19638845456 = pl [123, 109, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638845456 19638845440 19638779904 4 16 rfl, c36q50, c36q51]
  exact pl_leaf _ _ _ rfl

theorem c36q53 : Qm op_1239_candidate36 59904951508 = pl [54489, 102038, 74501, 26352, 4476, 288] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59904951508 40266106052 19638845456 rfl, c36q40, c36q52]
  exact pl_mul _ _ _ rfl

theorem c36q54 : Qm op_1239_candidate36 59904951511 = pl [264507, 420613, 265788, 83780, 13088, 800] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59904951511 59904951510 59904951508 0 1 rfl, c36q49, c36q53]
  exact pl_leaf _ _ _ rfl

theorem c36q55 : Qm op_1239_candidate36 59904951519 = pl [575565, 853687, 499360, 145932, 21360, 1248] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59904951519 59904951511 59904951510 3 0 rfl, c36q54, c36q49]
  exact pl_leaf _ _ _ rfl

theorem c36q56 : Qm op_1239_candidate36 59904951551 = pl [1104579, 1694913, 1030936, 313492, 47536, 2848] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59904951551 59904951519 59904951511 5 3 rfl, c36q55, c36q54]
  exact pl_leaf _ _ _ rfl

theorem c36q57 : Qm op_1239_candidate36 59904967935 = pl [2255709, 3402287, 2029656, 605356, 90256, 5344] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59904967935 59904951551 59904951519 14 5 rfl, c36q56, c36q55]
  exact pl_leaf _ _ _ rfl

theorem c36q58 : Qm op_1239_candidate36 59921745151 = pl [4464867, 6792113, 4091528, 1232340, 185328, 11040] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59921745151 59904967935 59904951551 24 14 rfl, c36q57, c36q56]
  exact pl_leaf _ _ _ rfl

theorem c36q59 : Qm op_1239_candidate36 40266106055 = pl [1567, 1731, 674, 116, 8] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266106055 40266106054 40266106052 0 1 rfl, c36q46, c36q40]
  exact pl_leaf _ _ _ rfl

theorem c36q60 : Qm op_1239_candidate36 40266106063 = pl [2929, 3445, 1494, 300, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266106063 40266106055 40266106054 3 0 rfl, c36q59, c36q46]
  exact pl_leaf _ _ _ rfl

theorem c36q61 : Qm op_1239_candidate36 40266106095 = pl [6063, 6907, 2842, 532, 40] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266106095 40266106063 40266106055 5 3 rfl, c36q60, c36q59]
  exact pl_leaf _ _ _ rfl

theorem c36q62 : Qm op_1239_candidate36 40266122479 = pl [11921, 13797, 5830, 1132, 88] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266122479 40266106095 40266106063 14 5 rfl, c36q61, c36q60]
  exact pl_leaf _ _ _ rfl

theorem c36q63 : Qm op_1239_candidate36 40282899695 = pl [24047, 27611, 11514, 2196, 168] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40282899695 40266122479 40266106095 24 14 rfl, c36q62, c36q61]
  exact pl_leaf _ _ _ rfl

theorem c36q64 : Qm op_1239_candidate36 59921745135 = pl [1947807, 3318606, 2223223, 751228, 135456, 11952, 336] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59921745135 40282899695 19638845440 rfl, c36q63, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q65 : Qm op_1239_candidate36 59921749247 = pl [8360481, 13429325, 8537974, 2734796, 456240, 34944, 672] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59921749247 59921745151 59921745135 12 4 rfl, c36q58, c36q64]
  exact pl_leaf _ _ _ rfl

theorem c36q66 : Qm op_1239_candidate36 59925943551 = pl [17290215, 27013551, 16721030, 5199476, 826896, 57024, 672] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59925943551 59921749247 59921745151 22 12 rfl, c36q65, c36q58]
  exact pl_leaf _ _ _ rfl

theorem c36q67 : Qm op_1239_candidate36 59904951494 = pl [55161, 100062, 73137, 27616, 5608, 544, 16] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59904951494 40266106054 19638845440 rfl, c36q46, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q68 : Qm op_1239_candidate36 59904955606 = pl [265851, 416661, 263060, 86308, 15352, 1312, 32] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59904955606 59904951510 59904951494 12 4 rfl, c36q49, c36q67]
  exact pl_leaf _ _ _ rfl

theorem c36q69 : Qm op_1239_candidate36 59909149910 = pl [576909, 849735, 496632, 148460, 23624, 1760, 32] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909149910 59904955606 59904951510 22 12 rfl, c36q68, c36q49]
  exact pl_leaf _ _ _ rfl

theorem c36q70 : Qm op_1239_candidate36 19638849552 = pl [285, 199, 28] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638849552 19638845456 19638845440 12 4 rfl, c36q52, c36q50]
  exact pl_leaf _ _ _ rfl

theorem c36q71 : Qm op_1239_candidate36 19643043856 = pl [531, 417, 76] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19643043856 19638849552 19638845456 22 12 rfl, c36q70, c36q52]
  exact pl_leaf _ _ _ rfl

theorem c36q72 : Qm op_1239_candidate36 59909149908 = pl [235233, 416778, 285989, 94628, 15036, 912] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59909149908 40266106052 19643043856 rfl, c36q40, c36q71]
  exact pl_mul _ _ _ rfl

theorem c36q73 : Qm op_1239_candidate36 59909149911 = pl [1047375, 1683291, 1068610, 337716, 53696, 3584, 32] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909149911 59909149910 59909149908 0 1 rfl, c36q69, c36q72]
  exact pl_leaf _ _ _ rfl

theorem c36q74 : Qm op_1239_candidate36 59909149919 = pl [2201193, 3382761, 2061874, 634636, 100944, 7104, 96] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909149919 59909149911 59909149910 3 0 rfl, c36q73, c36q69]
  exact pl_leaf _ _ _ rfl

theorem c36q75 : Qm op_1239_candidate36 16793600 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16793600 16777216 0 14 24 rfl, (Qm_single' op_1239_candidate36 16777216 24 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q76 : Qm op_1239_candidate36 59925943519 = pl [6603579, 12349476, 9568383, 3965782, 937468, 122256, 7392, 96] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59925943519 59909149919 16793600 rfl, c36q74, c36q75]
  exact pl_mul _ _ _ rfl

theorem c36q77 : Qm op_1239_candidate36 59925951743 = pl [30497373, 51712503, 35857796, 13131040, 2701832, 301536, 15456, 192] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59925951743 59925943551 59925943519 13 5 rfl, c36q66, c36q76]
  exact pl_leaf _ _ _ rfl

theorem c36q78 : Qm op_1239_candidate36 59926082815 = pl [65077803, 105739605, 69299856, 23529992, 4355624, 415584, 16800, 192] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59926082815 59925951743 59925943551 17 13 rfl, c36q77, c36q66]
  exact pl_leaf _ _ _ rfl

theorem c36q79 : Qm op_1239_candidate36 39191838790 = pl [73, 49, 6] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838790 39191838788 39191838784 1 2 rfl, c36q35, c36q28]
  exact pl_leaf _ _ _ rfl

theorem c36q80 : Qm op_1239_candidate36 39191838806 = pl [151, 95, 10] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838806 39191838790 39191838788 4 1 rfl, c36q79, c36q35]
  exact pl_leaf _ _ _ rfl

theorem c36q81 : Qm op_1239_candidate36 56683135062 = pl [3171, 3656, 1255, 110] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 56683135062 39191838806 17491296256 rfl, c36q80, c36q16]
  exact pl_mul _ _ _ rfl

theorem c36q82 : Qm op_1239_candidate36 58830684246 = pl [15297, 13669, 3538, 264] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58830684246 56683200598 56683135062 31 16 rfl, c36q25, c36q81]
  exact pl_leaf _ _ _ rfl

theorem c36q83 : Qm op_1239_candidate36 58830684244 = pl [4797, 7080, 3689, 770, 48] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 58830684244 39191838788 19638845456 rfl, c36q35, c36q52]
  exact pl_mul _ _ _ rfl

theorem c36q84 : Qm op_1239_candidate36 58830684247 = pl [24891, 27829, 10916, 1804, 96] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58830684247 58830684246 58830684244 0 1 rfl, c36q82, c36q83]
  exact pl_leaf _ _ _ rfl

theorem c36q85 : Qm op_1239_candidate36 58830684255 = pl [55485, 55167, 17992, 2332, 96] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58830684255 58830684247 58830684246 3 0 rfl, c36q84, c36q82]
  exact pl_leaf _ _ _ rfl

theorem c36q86 : Qm op_1239_candidate36 58830684287 = pl [105267, 110825, 39824, 5940, 288] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58830684287 58830684255 58830684247 5 3 rfl, c36q85, c36q84]
  exact pl_leaf _ _ _ rfl

theorem c36q87 : Qm op_1239_candidate36 58830700671 = pl [216237, 221159, 75808, 10604, 480] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58830700671 58830684287 58830684255 14 5 rfl, c36q86, c36q85]
  exact pl_leaf _ _ _ rfl

theorem c36q88 : Qm op_1239_candidate36 58847477887 = pl [426771, 442809, 155456, 22484, 1056] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58847477887 58830700671 58830684287 24 14 rfl, c36q87, c36q86]
  exact pl_leaf _ _ _ rfl

theorem c36q89 : Qm op_1239_candidate36 39191838791 = pl [151, 95, 10] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838791 39191838790 39191838788 0 1 rfl, c36q79, c36q35]
  exact pl_leaf _ _ _ rfl

theorem c36q90 : Qm op_1239_candidate36 39191838799 = pl [297, 193, 22] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838799 39191838791 39191838790 3 0 rfl, c36q89, c36q79]
  exact pl_leaf _ _ _ rfl

theorem c36q91 : Qm op_1239_candidate36 39191838831 = pl [599, 383, 42] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191838831 39191838799 39191838791 5 3 rfl, c36q90, c36q89]
  exact pl_leaf _ _ _ rfl

theorem c36q92 : Qm op_1239_candidate36 39191855215 = pl [1193, 769, 86] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39191855215 39191838831 39191838799 14 5 rfl, c36q91, c36q90]
  exact pl_leaf _ _ _ rfl

theorem c36q93 : Qm op_1239_candidate36 39208632431 = pl [2391, 1535, 170] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 39208632431 39191855215 39191838831 24 14 rfl, c36q92, c36q91]
  exact pl_leaf _ _ _ rfl

theorem c36q94 : Qm op_1239_candidate36 58847477871 = pl [193671, 231930, 87627, 10720, 340] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 58847477871 39208632431 19638845440 rfl, c36q93, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q95 : Qm op_1239_candidate36 58847481983 = pl [814113, 906669, 330710, 43924, 1736] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58847481983 58847477887 58847477871 12 4 rfl, c36q88, c36q94]
  exact pl_leaf _ _ _ rfl

theorem c36q96 : Qm op_1239_candidate36 58851676287 = pl [1667655, 1792287, 641622, 88892, 3848] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58851676287 58847481983 58847477887 22 12 rfl, c36q95, c36q88]
  exact pl_leaf _ _ _ rfl

theorem c36q97 : Qm op_1239_candidate36 58830684230 = pl [5913, 7254, 2837, 368, 12] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 58830684230 39191838790 19638845440 rfl, c36q79, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q98 : Qm op_1239_candidate36 58830688342 = pl [27123, 28177, 9212, 1000, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58830688342 58830684246 58830684230 12 4 rfl, c36q82, c36q97]
  exact pl_leaf _ _ _ rfl

theorem c36q99 : Qm op_1239_candidate36 58834882646 = pl [57717, 55515, 16288, 1528, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58834882646 58830688342 58830684246 22 12 rfl, c36q98, c36q82]
  exact pl_leaf _ _ _ rfl

theorem c36q100 : Qm op_1239_candidate36 58834882644 = pl [20709, 28476, 13617, 2582, 152] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 58834882644 39191838788 19643043856 rfl, c36q35, c36q71]
  exact pl_mul _ _ _ rfl

theorem c36q101 : Qm op_1239_candidate36 58834882647 = pl [99135, 112467, 43522, 6692, 328] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58834882647 58834882646 58834882644 0 1 rfl, c36q99, c36q100]
  exact pl_leaf _ _ _ rfl

theorem c36q102 : Qm op_1239_candidate36 58834882655 = pl [214569, 223497, 76098, 9748, 376] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58834882655 58834882647 58834882646 3 0 rfl, c36q101, c36q99]
  exact pl_leaf _ _ _ rfl

theorem c36q103 : Qm op_1239_candidate36 58851676255 = pl [643707, 885060, 451791, 105342, 10876, 376] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 58851676255 58834882655 16793600 rfl, c36q102, c36q75]
  exact pl_mul _ _ _ rfl

theorem c36q104 : Qm op_1239_candidate36 58851684479 = pl [2955069, 3562407, 1545204, 299576, 25600, 752] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58851684479 58851676287 58851676255 13 5 rfl, c36q96, c36q103]
  exact pl_leaf _ _ _ rfl

theorem c36q105 : Qm op_1239_candidate36 58851815551 = pl [6290379, 7146981, 2828448, 477360, 33296, 752] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 58851815551 58851684479 58851676287 17 13 rfl, c36q104, c36q96]
  exact pl_leaf _ _ _ rfl

theorem c36q106 : Qm op_1239_candidate36 59926082687 = pl [31451895, 54606042, 35583183, 10872144, 1598560, 103648, 2256] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59926082687 58851815551 1074267136 rfl, c36q105, c36q42]
  exact pl_mul _ _ _ rfl

theorem c36q107 : Qm op_1239_candidate36 59926115583 = pl [127981593, 214951689, 140466222, 45274280, 7552744, 622880, 21312, 192] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59926115583 59926082815 59926082687 15 7 rfl, c36q78, c36q106]
  exact pl_leaf _ _ _ rfl

theorem c36q108 : Qm op_1239_candidate36 17491361942 = pl [639, 363, 22] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491361942 17491361814 17491361810 7 2 rfl, c36q22, c36q21]
  exact pl_leaf _ _ _ rfl

theorem c36q109 : Qm op_1239_candidate36 17491362966 = pl [1281, 725, 42] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 17491362966 17491361942 17491361814 10 7 rfl, c36q108, c36q22]
  exact pl_leaf _ _ _ rfl

theorem c36q110 : Qm op_1239_candidate36 18565104790 = pl [2559, 1451, 86] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 18565104790 17491362966 17491361942 30 10 rfl, c36q109, c36q108]
  exact pl_leaf _ _ _ rfl

theorem c36q111 : Qm op_1239_candidate36 18565103766 = pl [639, 1002, 385, 22] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 18565103766 17491361942 1073741824 rfl, c36q108, (Qm_single' op_1239_candidate36 1073741824 30 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q112 : Qm op_1239_candidate36 18565629078 = pl [3837, 3455, 856, 44] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 18565629078 18565104790 18565103766 19 10 rfl, c36q110, c36q111]
  exact pl_leaf _ _ _ rfl

theorem c36q113 : Qm op_1239_candidate36 1074267268 = pl [17, 13, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267268 1074267264 1074267136 2 7 rfl, c36q44, c36q42]
  exact pl_leaf _ _ _ rfl

theorem c36q114 : Qm op_1239_candidate36 1074267270 = pl [31, 27, 6] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267270 1074267268 1074267264 1 2 rfl, c36q113, c36q44]
  exact pl_leaf _ _ _ rfl

theorem c36q115 : Qm op_1239_candidate36 1074267286 = pl [65, 53, 10] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267286 1074267270 1074267268 4 1 rfl, c36q114, c36q113]
  exact pl_leaf _ _ _ rfl

theorem c36q116 : Qm op_1239_candidate36 18565563542 = pl [1365, 1828, 793, 110] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 18565563542 1074267286 17491296256 rfl, c36q115, c36q16]
  exact pl_mul _ _ _ rfl

theorem c36q117 : Qm op_1239_candidate36 20713112726 = pl [6567, 7111, 2442, 264] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20713112726 18565629078 18565563542 31 16 rfl, c36q112, c36q116]
  exact pl_leaf _ _ _ rfl

theorem c36q118 : Qm op_1239_candidate36 20713112724 = pl [2091, 3452, 2071, 530, 48] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20713112724 1074267268 19638845456 rfl, c36q113, c36q52]
  exact pl_mul _ _ _ rfl

theorem c36q119 : Qm op_1239_candidate36 20713112727 = pl [10749, 14015, 6584, 1324, 96] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20713112727 20713112726 20713112724 0 1 rfl, c36q117, c36q118]
  exact pl_leaf _ _ _ rfl

theorem c36q120 : Qm op_1239_candidate36 20713112735 = pl [23883, 28237, 11468, 1852, 96] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20713112735 20713112727 20713112726 3 0 rfl, c36q119, c36q117]
  exact pl_leaf _ _ _ rfl

theorem c36q121 : Qm op_1239_candidate36 20713112767 = pl [45381, 56267, 24636, 4500, 288] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20713112767 20713112735 20713112727 5 3 rfl, c36q120, c36q119]
  exact pl_leaf _ _ _ rfl

theorem c36q122 : Qm op_1239_candidate36 20713129151 = pl [93147, 112741, 47572, 8204, 480] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20713129151 20713112767 20713112735 14 5 rfl, c36q121, c36q120]
  exact pl_leaf _ _ _ rfl

theorem c36q123 : Qm op_1239_candidate36 20729906367 = pl [183909, 225275, 96844, 17204, 1056] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20729906367 20713129151 20713112767 24 14 rfl, c36q122, c36q121]
  exact pl_leaf _ _ _ rfl

theorem c36q124 : Qm op_1239_candidate36 1074267271 = pl [65, 53, 10] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267271 1074267270 1074267268 0 1 rfl, c36q114, c36q113]
  exact pl_leaf _ _ _ rfl

theorem c36q125 : Qm op_1239_candidate36 1074267279 = pl [127, 107, 22] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267279 1074267271 1074267270 3 0 rfl, c36q124, c36q114]
  exact pl_leaf _ _ _ rfl

theorem c36q126 : Qm op_1239_candidate36 1074267311 = pl [257, 213, 42] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074267311 1074267279 1074267271 5 3 rfl, c36q125, c36q124]
  exact pl_leaf _ _ _ rfl

theorem c36q127 : Qm op_1239_candidate36 1074283695 = pl [511, 427, 86] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074283695 1074267311 1074267279 14 5 rfl, c36q126, c36q125]
  exact pl_leaf _ _ _ rfl

theorem c36q128 : Qm op_1239_candidate36 1091060911 = pl [1025, 853, 170] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1091060911 1074283695 1074267311 24 14 rfl, c36q127, c36q126]
  exact pl_leaf _ _ _ rfl

theorem c36q129 : Qm op_1239_candidate36 20729906351 = pl [83025, 115218, 54205, 9356, 340] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20729906351 1091060911 19638845440 rfl, c36q128, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q130 : Qm op_1239_candidate36 20729910463 = pl [349959, 455711, 205254, 35916, 1736] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20729910463 20729906367 20729906351 12 4 rfl, c36q123, c36q129]
  exact pl_leaf _ _ _ rfl

theorem c36q131 : Qm op_1239_candidate36 20734104767 = pl [717777, 906261, 398942, 70324, 3848] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20734104767 20729910463 20729906367 22 12 rfl, c36q130, c36q123]
  exact pl_leaf _ _ _ rfl

theorem c36q132 : Qm op_1239_candidate36 20713112710 = pl [2511, 3582, 1763, 324, 12] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20713112710 1074267270 19638845440 rfl, c36q114, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q133 : Qm op_1239_candidate36 20713116822 = pl [11589, 14275, 5968, 912, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20713116822 20713112726 20713112710 12 4 rfl, c36q117, c36q132]
  exact pl_leaf _ _ _ rfl

theorem c36q134 : Qm op_1239_candidate36 20717311126 = pl [24723, 28497, 10852, 1440, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20717311126 20713116822 20713112726 22 12 rfl, c36q133, c36q117]
  exact pl_leaf _ _ _ rfl

theorem c36q135 : Qm op_1239_candidate36 20717311124 = pl [9027, 13992, 7775, 1822, 152] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20717311124 1074267268 19643043856 rfl, c36q113, c36q71]
  exact pl_mul _ _ _ rfl

theorem c36q136 : Qm op_1239_candidate36 20717311127 = pl [42777, 56481, 26402, 5084, 328] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20717311127 20717311126 20717311124 0 1 rfl, c36q134, c36q135]
  exact pl_leaf _ _ _ rfl

theorem c36q137 : Qm op_1239_candidate36 20717311135 = pl [92223, 113475, 48106, 7964, 376] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20717311135 20717311127 20717311126 3 0 rfl, c36q136, c36q134]
  exact pl_leaf _ _ _ rfl

theorem c36q138 : Qm op_1239_candidate36 20734104735 = pl [276669, 432648, 257793, 71998, 9092, 376] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20734104735 20717311135 16793600 rfl, c36q137, c36q75]
  exact pl_mul _ _ _ rfl

theorem c36q139 : Qm op_1239_candidate36 20734112959 = pl [1271115, 1771557, 914528, 214320, 22032, 752] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20734112959 20734104767 20734104735 13 5 rfl, c36q131, c36q138]
  exact pl_leaf _ _ _ rfl

theorem c36q140 : Qm op_1239_candidate36 20734244031 = pl [2706669, 3584079, 1712412, 354968, 29728, 752] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20734244031 20734112959 20734104767 17 13 rfl, c36q139, c36q131]
  exact pl_leaf _ _ _ rfl

theorem c36q141 : Qm op_1239_candidate36 19638845458 = pl [285, 199, 28] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638845458 19638845456 19638845440 1 4 rfl, c36q52, c36q50]
  exact pl_leaf _ _ _ rfl

theorem c36q142 : Qm op_1239_candidate36 19638845459 = pl [531, 417, 76] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638845459 19638845458 19638845456 0 1 rfl, c36q141, c36q52]
  exact pl_leaf _ _ _ rfl

theorem c36q143 : Qm op_1239_candidate36 19638845467 = pl [1101, 815, 132] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638845467 19638845459 19638845458 3 0 rfl, c36q142, c36q141]
  exact pl_leaf _ _ _ rfl

theorem c36q144 : Qm op_1239_candidate36 19638845499 = pl [2163, 1649, 284] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638845499 19638845467 19638845459 5 3 rfl, c36q143, c36q142]
  exact pl_leaf _ _ _ rfl

theorem c36q145 : Qm op_1239_candidate36 19638861883 = pl [4365, 3279, 548] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19638861883 19638845499 19638845467 14 5 rfl, c36q144, c36q143]
  exact pl_leaf _ _ _ rfl

theorem c36q146 : Qm op_1239_candidate36 19655639099 = pl [8691, 6577, 1116] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19655639099 19638861883 19638845499 24 14 rfl, c36q145, c36q144]
  exact pl_leaf _ _ _ rfl

theorem c36q147 : Qm op_1239_candidate36 16793632 = pl [5, 3] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16793632 16793600 16777216 5 14 rfl, c36q75, (Qm_single' op_1239_candidate36 16777216 24 rfl)]
  exact pl_leaf _ _ _ rfl

theorem c36q148 : Qm op_1239_candidate36 16793640 = pl [11, 5] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16793640 16793632 16793600 3 5 rfl, c36q147, c36q75]
  exact pl_leaf _ _ _ rfl

theorem c36q149 : Qm op_1239_candidate36 16793641 = pl [21, 11] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16793641 16793640 16793632 0 3 rfl, c36q148, c36q147]
  exact pl_leaf _ _ _ rfl

theorem c36q150 : Qm op_1239_candidate36 16793643 = pl [43, 21] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16793643 16793641 16793640 1 0 rfl, c36q149, c36q148]
  exact pl_leaf _ _ _ rfl

theorem c36q151 : Qm op_1239_candidate36 19655639083 = pl [3483, 3636, 1031, 42] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 19655639083 16793643 19638845440 rfl, c36q150, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q152 : Qm op_1239_candidate36 19655643195 = pl [15657, 13849, 3178, 84] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19655643195 19655639099 19655639083 12 4 rfl, c36q146, c36q151]
  exact pl_leaf _ _ _ rfl

theorem c36q153 : Qm op_1239_candidate36 19659837499 = pl [33039, 27003, 5410, 84] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19659837499 19655643195 19655639099 22 12 rfl, c36q152, c36q146]
  exact pl_leaf _ _ _ rfl

theorem c36q154 : Qm op_1239_candidate36 4198400 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 4198400 4194304 0 12 22 rfl, (Qm_single' op_1239_candidate36 4194304 22 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q155 : Qm op_1239_candidate36 19643043840 = pl [243, 216, 51, 2] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 19643043840 4198400 19638845440 rfl, c36q154, c36q50]
  exact pl_mul _ _ _ rfl

theorem c36q156 : Qm op_1239_candidate36 19643043858 = pl [1017, 849, 178, 4] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19643043858 19643043856 19643043840 1 4 rfl, c36q71, c36q155]
  exact pl_leaf _ _ _ rfl

theorem c36q157 : Qm op_1239_candidate36 19643043859 = pl [2079, 1683, 330, 4] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19643043859 19643043858 19643043856 0 1 rfl, c36q156, c36q71]
  exact pl_leaf _ _ _ rfl

theorem c36q158 : Qm op_1239_candidate36 19643043867 = pl [4113, 3381, 686, 12] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19643043867 19643043859 19643043858 3 0 rfl, c36q157, c36q156]
  exact pl_leaf _ _ _ rfl

theorem c36q159 : Qm op_1239_candidate36 19659837467 = pl [12339, 14256, 5439, 722, 12] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 19659837467 19643043867 16793600 rfl, c36q158, c36q75]
  exact pl_mul _ _ _ rfl

theorem c36q160 : Qm op_1239_candidate36 19659845691 = pl [57717, 55515, 16288, 1528, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19659845691 19659837499 19659837467 13 5 rfl, c36q153, c36q159]
  exact pl_leaf _ _ _ rfl

theorem c36q161 : Qm op_1239_candidate36 19659976763 = pl [123795, 109521, 27108, 1696, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19659976763 19659845691 19659837499 17 13 rfl, c36q160, c36q153]
  exact pl_leaf _ _ _ rfl

theorem c36q162 : Qm op_1239_candidate36 16801824 = pl [11, 5] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16801824 16793632 16793600 13 5 rfl, c36q147, c36q75]
  exact pl_leaf _ _ _ rfl

theorem c36q163 : Qm op_1239_candidate36 16932896 = pl [21, 11] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16932896 16801824 16793632 17 13 rfl, c36q162, c36q147]
  exact pl_leaf _ _ _ rfl

theorem c36q164 : Qm op_1239_candidate36 139264 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 139264 131072 0 13 17 rfl, (Qm_single' op_1239_candidate36 131072 17 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q165 : Qm op_1239_candidate36 16932864 = pl [9, 6, 1] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 16932864 139264 16793600 rfl, c36q164, c36q75]
  exact pl_mul _ _ _ rfl

theorem c36q166 : Qm op_1239_candidate36 16932904 = pl [39, 23, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16932904 16932896 16932864 3 5 rfl, c36q163, c36q165]
  exact pl_leaf _ _ _ rfl

theorem c36q167 : Qm op_1239_candidate36 16932905 = pl [81, 45, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 16932905 16932904 16932896 0 3 rfl, c36q166, c36q163]
  exact pl_leaf _ _ _ rfl

theorem c36q168 : Qm op_1239_candidate36 19659976761 = pl [43011, 57672, 25983, 4254, 152] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 19659976761 16932905 19643043856 rfl, c36q167, c36q71]
  exact pl_mul _ _ _ rfl

theorem c36q169 : Qm op_1239_candidate36 19659976767 = pl [209817, 224865, 79074, 10204, 328] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19659976767 19659976763 19659976761 2 1 rfl, c36q161, c36q168]
  exact pl_leaf _ _ _ rfl

theorem c36q170 : Qm op_1239_candidate36 20734243903 = pl [1049085, 1753776, 1069965, 288242, 32252, 984] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20734243903 19659976767 1074267136 rfl, c36q169, c36q42]
  exact pl_mul _ _ _ rfl

theorem c36q171 : Qm op_1239_candidate36 20734276799 = pl [4804839, 7091631, 3852342, 931452, 94232, 2720] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20734276799 20734244031 20734243903 15 7 rfl, c36q140, c36q170]
  exact pl_leaf _ _ _ rfl

theorem c36q172 : Qm op_1239_candidate36 59926115519 = pl [52853229, 102032136, 77833917, 29507682, 5693812, 501080, 13600] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59926115519 20734276799 39191838720 rfl, c36q171, c36q26]
  exact pl_mul _ _ _ rfl

theorem c36q173 : Qm op_1239_candidate36 59926116095 = pl [233688051, 419015961, 296134056, 104289644, 18940368, 1625040, 48512, 192] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59926116095 59926115583 59926115519 9 6 rfl, c36q107, c36q172]
  exact pl_leaf _ _ _ rfl

theorem c36q174 : Qm op_1239_candidate36 59909149782 = pl [288585, 450726, 247985, 56504, 4704, 72] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59909149782 58834882646 1074267136 rfl, c36q99, c36q42]
  exact pl_mul _ _ _ rfl

theorem c36q175 : Qm op_1239_candidate36 59909182678 = pl [1154079, 1751187, 992602, 261468, 33032, 1904, 32] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909182678 59909149910 59909149782 15 7 rfl, c36q69, c36q174]
  exact pl_leaf _ _ _ rfl

theorem c36q176 : Qm op_1239_candidate36 19643043862 = pl [2079, 1683, 330, 4] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 19643043862 19643043858 19643043856 2 1 rfl, c36q156, c36q71]
  exact pl_leaf _ _ _ rfl

theorem c36q177 : Qm op_1239_candidate36 20717310998 = pl [10395, 14652, 6699, 1010, 12] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 20717310998 19643043862 1074267136 rfl, c36q176, c36q42]
  exact pl_mul _ _ _ rfl

theorem c36q178 : Qm op_1239_candidate36 20717343894 = pl [45513, 57801, 24250, 3460, 48] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 20717343894 20717311126 20717310998 15 7 rfl, c36q134, c36q177]
  exact pl_leaf _ _ _ rfl

theorem c36q179 : Qm op_1239_candidate36 59909182614 = pl [500643, 863376, 555755, 159310, 17828, 240] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59909182614 20717343894 39191838720 rfl, c36q178, c36q26]
  exact pl_mul _ _ _ rfl

theorem c36q180 : Qm op_1239_candidate36 59909183190 = pl [2155365, 3477939, 2104112, 580088, 68688, 2384, 32] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909183190 59909182678 59909182614 9 6 rfl, c36q175, c36q179]
  exact pl_leaf _ _ _ rfl

theorem c36q181 : Qm op_1239_candidate36 59926116094 = pl [84059235, 185213016, 166363695, 77973886, 20229080, 2832976, 193456, 5504, 64] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59926116094 59909183190 16932904 rfl, c36q180, c36q166]
  exact pl_mul _ _ _ rfl

theorem c36q182 : Qm op_1239_candidate36 59926116351 = pl [401806521, 789441993, 628861446, 260237416, 59398528, 7290992, 435424, 11200, 128] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59926116351 59926116095 59926116094 8 0 rfl, c36q173, c36q181]
  exact pl_leaf _ _ _ rfl

theorem c36q183 : Qm op_1239_candidate36 59926118399 = pl [869182623, 1627473915, 1221129558, 468816704, 97279264, 10541072, 532448, 11584, 128] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59926118399 59926116351 59926116095 11 8 rfl, c36q182, c36q173]
  exact pl_leaf _ _ _ rfl

theorem c36q184 : Qm op_1239_candidate36 68516052991 = pl [1672795665, 3206357901, 2478852450, 989291536, 216076320, 25123056, 1403296, 33984, 384] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68516052991 59926118399 59926116351 33 11 rfl, c36q183, c36q182]
  exact pl_leaf _ _ _ rfl

theorem c36q185 : Qm op_1239_candidate36 68516050943 = pl [401806521, 1191248514, 1418303439, 889098862, 319635944, 66689520, 7726416, 446624, 11328, 128] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 68516050943 59926116351 8589934592 rfl, c36q182, (Qm_single' op_1239_candidate36 8589934592 33 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q186 : Qm op_1239_candidate36 68650270719 = pl [2476408707, 5588854929, 5315459328, 2767489260, 855348208, 158502096, 16856128, 927232, 23040, 256] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68650270719 68516052991 68516050943 27 11 rfl, c36q184, c36q185]
  exact pl_leaf _ _ _ rfl

theorem c36q187 : Qm op_1239_candidate36 8589936640 = pl [3, 1] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 8589936640 8589934592 0 11 33 rfl, (Qm_single' op_1239_candidate36 8589934592 33 rfl), (Qm_zero op_1239_candidate36)]
  exact pl_leaf _ _ _ rfl

theorem c36q188 : Qm op_1239_candidate36 8724154368 = pl [5, 3] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 8724154368 8589936640 8589934592 27 11 rfl, c36q187, (Qm_single' op_1239_candidate36 8589934592 33 rfl)]
  exact pl_leaf _ _ _ rfl

theorem c36q189 : Qm op_1239_candidate36 68650270463 = pl [1168440255, 2796143958, 2737718163, 1409850388, 407570772, 64946304, 5117680, 146496, 576] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 68650270463 59926116095 8724154368 rfl, c36q173, c36q188]
  exact pl_mul _ _ _ rfl

theorem c36q190 : Qm op_1239_candidate36 68717379583 = pl [4813289217, 11181142845, 10790895654, 5587190036, 1670489752, 288394704, 27091488, 1220224, 24192, 256] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68717379583 68650270719 68650270463 26 8 rfl, c36q186, c36q189]
  exact pl_leaf _ _ _ rfl

theorem c36q191 : Qm op_1239_candidate36 40266105924 = pl [195, 232, 79, 6] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 40266105924 39191838788 1074267136 rfl, c36q35, c36q42]
  exact pl_mul _ _ _ rfl

theorem c36q192 : Qm op_1239_candidate36 40266138820 = pl [833, 901, 290, 24] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266138820 40266106052 40266105924 15 7 rfl, c36q40, c36q191]
  exact pl_leaf _ _ _ rfl

theorem c36q193 : Qm op_1239_candidate36 1074300032 = pl [17, 13, 2] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074300032 1074267264 1074267136 15 7 rfl, c36q44, c36q42]
  exact pl_leaf _ _ _ rfl

theorem c36q194 : Qm op_1239_candidate36 1074299904 = pl [5, 8, 3] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 1074299904 1074267136 32768 rfl, c36q42, (Qm_single' op_1239_candidate36 32768 15 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q195 : Qm op_1239_candidate36 1074300036 = pl [27, 29, 8] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 1074300036 1074300032 1074299904 2 7 rfl, c36q193, c36q194]
  exact pl_leaf _ _ _ rfl

theorem c36q196 : Qm op_1239_candidate36 40266138756 = pl [297, 454, 233, 40] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 40266138756 1074300036 39191838720 rfl, c36q195, c36q26]
  exact pl_mul _ _ _ rfl

theorem c36q197 : Qm op_1239_candidate36 40266139332 = pl [1427, 1809, 756, 104] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 40266139332 40266138820 40266138756 9 6 rfl, c36q192, c36q196]
  exact pl_leaf _ _ _ rfl

theorem c36q198 : Qm op_1239_candidate36 59909183188 = pl [757737, 1555638, 1264241, 507960, 100824, 7904] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 59909183188 40266139332 19643043856 rfl, c36q197, c36q71]
  exact pl_mul _ _ _ rfl

theorem c36q199 : Qm op_1239_candidate36 59909183191 = pl [3670839, 6589215, 4632594, 1596008, 270336, 18192, 32] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909183191 59909183190 59909183188 0 1 rfl, c36q180, c36q198]
  exact pl_leaf _ _ _ rfl

theorem c36q200 : Qm op_1239_candidate36 59909183447 = pl [7981569, 13545093, 8840818, 2756184, 407712, 22960, 96] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909183447 59909183191 59909183190 8 0 rfl, c36q199, c36q180]
  exact pl_leaf _ _ _ rfl

theorem c36q201 : Qm op_1239_candidate36 59909185495 = pl [15323247, 26723523, 18106006, 5948200, 948384, 59344, 160] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 59909185495 59909183447 59909183191 11 8 rfl, c36q200, c36q199]
  exact pl_leaf _ _ _ rfl

theorem c36q202 : Qm op_1239_candidate36 68499120087 = pl [31286385, 53813709, 35787642, 11460568, 1763808, 105264, 352] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68499120087 59909185495 59909183447 33 11 rfl, c36q201, c36q200]
  exact pl_leaf _ _ _ rfl

theorem c36q203 : Qm op_1239_candidate36 68499118039 = pl [7981569, 21526662, 22385911, 11597002, 3163896, 430672, 23056, 96] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 68499118039 59909183447 8589934592 rfl, c36q200, (Qm_single' op_1239_candidate36 8589934592 33 rfl)]
  exact pl_mul _ _ _ rfl

theorem c36q204 : Qm op_1239_candidate36 68633337815 = pl [47249523, 96867033, 80559464, 34654572, 8091600, 966608, 46464, 192] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68633337815 68499120087 68499118039 27 11 rfl, c36q202, c36q203]
  exact pl_leaf _ _ _ rfl

theorem c36q205 : Qm op_1239_candidate36 68633337559 = pl [18354195, 43958592, 42930615, 21877822, 6139704, 901968, 54736, 96] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 68633337559 59909183191 8724154368 rfl, c36q199, c36q188]
  exact pl_mul _ _ _ rfl

theorem c36q206 : Qm op_1239_candidate36 68700446679 = pl [83957913, 184784217, 166420694, 78410216, 20371008, 2770544, 155936, 384] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68700446679 68633337815 68633337559 26 8 rfl, c36q204, c36q205]
  exact pl_leaf _ _ _ rfl

theorem c36q207 : Qm op_1239_candidate36 68717379575 = pl [1763116173, 4804005600, 5527460961, 3477242170, 1290303544, 282262512, 33750640, 1723360, 4224] := by
  rw [cutM op_1239_candidate36 nb36 hnb36 68717379575 68700446679 16932896 rfl, c36q206, c36q163]
  exact pl_mul _ _ _ rfl

theorem c36q208 : Qm op_1239_candidate36 68719476735 = pl [8339521563, 20789154045, 21845817576, 12541674376, 4251096840, 852919728, 94592768, 4666944, 32640, 256] := by
  rw [leafM op_1239_candidate36 nb36 hnb36 68719476735 68717379583 68717379575 21 3 rfl, c36q190, c36q207]
  exact pl_leaf _ _ _ rfl

theorem c36_poly : petrial_nullity_poly op_1239_candidate36 =
    pl [8339521563, 20789154045, 21845817576, 12541674376, 4251096840, 852919728, 94592768, 4666944, 32640, 256] := by
  rw [← c36q208]
  unfold Qm
  apply petrial_nullity_poly_iso
  refine (SimpleGraph.induceUnivIso op_1239_candidate36).symm.trans (isoOfEq _ ?_)
  ext x
  show True ↔ (68719476735 : ℕ).testBit x.val = true
  rw [show (68719476735 : ℕ) = 2 ^ 36 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  simp

end

end Op1239C36Cert

theorem op_1239_candidate36_petrial_coefficients : letI : DecidableRel op_1239_candidate36.Adj := Classical.decRel _; petrial_coeff op_1239_candidate36 27 = 256 ∧ petrial_coeff op_1239_candidate36 28 = 32640 ∧ petrial_coeff op_1239_candidate36 29 = 4666944 := by
  letI : DecidableRel op_1239_candidate36.Adj := Classical.decRel _
  have hk : ∀ k, k ≤ 36 → petrial_coeff op_1239_candidate36 k =
      (Op1239C36Cert.pl [8339521563, 20789154045, 21845817576, 12541674376, 4251096840, 852919728, 94592768, 4666944, 32640, 256]).coeff (36 - k) := by
    intro k hk
    rw [← Op1239C36Cert.c36_poly, ← petrial_nullity_poly_coeff_eq_petrial_coeff op_1239_candidate36 (by simpa using hk)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hk 27 (by norm_num), Op1239C36Cert.pl_coeff]; rfl
  · rw [hk 28 (by norm_num), Op1239C36Cert.pl_coeff]; rfl
  · rw [hk 29 (by norm_num), Op1239C36Cert.pl_coeff]; rfl
