import AFTD.Prelude
import AFTD.Kb.Tcs.BibdIsomorphicOfBlockCliqueGraphIsoOfThreeLe
import AFTD.Kb.Tcs.BibdBlockCliqueGraph
import AFTD.Kb.Tcs.BibdIsomorphic
import AFTD.Kb.Tcs.BIBD
import AFTD.Kb.Tcs.G

/-!
# bibd_isomorphic_of_block_clique_graph_iso

Topic: graphs   Node: 81b42f9d768c

Provenance: original. Related work: arXiv:2611.05762, Conjecture 6.30.1 (Sec. 6.30, Algebraic Recoverability), for the construction of Sec. 6.9. Stated for every block size k; finiteness of the block sets is added because Nat.card gives no information on infinite types.

OP-1148: if two BIBDs D₁, D₂ with the same parameters (v, b, r, k, λ) on finite block sets have isomorphic modified block-clique graphs (bibd_block_clique_graph), then the designs are isomorphic (bibd_isomorphic), for every block size k.
-/

open Classical

theorem bibd_isomorphic_of_k_zero {X₁ B₁ X₂ B₂ : Type*} [Finite B₁] [Finite B₂]
    {v b r lam : ℕ} (D₁ : BIBD X₁ B₁ v b r 0 lam) (D₂ : BIBD X₂ B₂ v b r 0 lam) :
    bibd_isomorphic D₁ D₂ := by
  have hv : v ≠ 0 := by
    have := D₁.incomplete
    omega
  have fx1 : Finite X₁ := Nat.finite_of_card_ne_zero (by rw [D₁.card_points]; exact hv)
  have fx2 : Finite X₂ := Nat.finite_of_card_ne_zero (by rw [D₂.card_points]; exact hv)
  have hX : Nonempty (X₁ ≃ X₂) := Finite.card_eq.mp (by rw [D₁.card_points, D₂.card_points])
  have hB : Nonempty (B₁ ≃ B₂) := Finite.card_eq.mp (by rw [D₁.card_blocks, D₂.card_blocks])
  rcases hX with ⟨f⟩
  rcases hB with ⟨g⟩
  refine ⟨f, g, fun b₁ x => ?_⟩
  constructor
  · rintro ⟨j, _⟩; exact Fin.elim0 j
  · rintro ⟨j', _⟩; exact Fin.elim0 j'

theorem bibd_isomorphic_of_k_one {X₁ B₁ X₂ B₂ : Type*} [Finite B₁] [Finite B₂]
    {v b r lam : ℕ} (D₁ : BIBD X₁ B₁ v b r 1 lam) (D₂ : BIBD X₂ B₂ v b r 1 lam) :
    bibd_isomorphic D₁ D₂ := by
  have hv : v ≠ 0 := by
    have := D₁.incomplete
    omega
  have fx1 : Finite X₁ := Nat.finite_of_card_ne_zero (by rw [D₁.card_points]; exact hv)
  have fx2 : Finite X₂ := Nat.finite_of_card_ne_zero (by rw [D₂.card_points]; exact hv)
  have hX : Nonempty (X₁ ≃ X₂) := Finite.card_eq.mp (by rw [D₁.card_points, D₂.card_points])
  rcases hX with ⟨f⟩
  let j0 : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  let pt₁ : B₁ → X₁ := fun β => D₁.block_pts β j0
  let pt₂ : B₂ → X₂ := fun β => D₂.block_pts β j0
  have h_fib₁ : ∀ x : X₁, Nat.card { β : B₁ // pt₁ β = x } = r := by
    intro x
    have hr := D₁.replication x
    have heq : { β : B₁ // pt₁ β = x } ≃ { β : B₁ // ∃ j, D₁.block_pts β j = x } :=
      Equiv.subtypeEquivRight (fun β => by
        constructor
        · intro h; exact ⟨j0, h⟩
        · rintro ⟨j, hj⟩
          have : j = j0 := Subsingleton.elim j j0
          subst this
          exact hj)
    rw [Nat.card_congr heq]
    exact hr
  have h_fib₂ : ∀ y : X₂, Nat.card { β : B₂ // pt₂ β = y } = r := by
    intro y
    have hr := D₂.replication y
    have heq : { β : B₂ // pt₂ β = y } ≃ { β : B₂ // ∃ j, D₂.block_pts β j = y } :=
      Equiv.subtypeEquivRight (fun β => by
        constructor
        · intro h; exact ⟨j0, h⟩
        · rintro ⟨j, hj⟩
          have : j = j0 := Subsingleton.elim j j0
          subst this
          exact hj)
    rw [Nat.card_congr heq]
    exact hr
  have h_fib_iso : ∀ x : X₁, Nonempty ({ β : B₁ // pt₁ β = x } ≃ { β : B₂ // pt₂ β = f x }) := by
    intro x
    exact Finite.card_eq.mp (by rw [h_fib₁, h_fib₂])
  let e₁ : B₁ ≃ (x : X₁) × { β : B₁ // pt₁ β = x } :=
    { toFun := fun β => ⟨pt₁ β, ⟨β, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun β => rfl
      right_inv := fun ⟨x, β, hβ⟩ => by
        dsimp
        subst hβ
        rfl }
  let e₂ : B₂ ≃ (y : X₂) × { β : B₂ // pt₂ β = y } :=
    { toFun := fun β => ⟨pt₂ β, ⟨β, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun β => rfl
      right_inv := fun ⟨y, β, hβ⟩ => by
        dsimp
        subst hβ
        rfl }
  let e_sigma : ((x : X₁) × { β : B₁ // pt₁ β = x }) ≃ ((y : X₂) × { β : B₂ // pt₂ β = y }) :=
    Equiv.sigmaCongr f (fun x => (h_fib_iso x).some)
  let g : B₁ ≃ B₂ := e₁.trans (e_sigma.trans e₂.symm)
  refine ⟨f, g, fun β x => ?_⟩
  have hg_pt : pt₂ (g β) = f (pt₁ β) := by
    have this1 : (e_sigma (e₁ β)).1 = f (pt₁ β) := rfl
    have he2 : (e₂ (g β)).1 = (e_sigma (e₁ β)).1 := by
      change (e₂ (e₂.symm (e_sigma (e₁ β)))).1 = (e_sigma (e₁ β)).1
      rw [e₂.apply_symm_apply]
    exact he2.trans this1
  constructor
  · rintro ⟨j, hj⟩
    have hj0 : j = j0 := Subsingleton.elim j j0
    subst hj0
    refine ⟨j0, ?_⟩
    change pt₂ (g β) = f x
    rw [hg_pt]
    exact congr_arg f hj
  · rintro ⟨j', hj'⟩
    have hj0 : j' = j0 := Subsingleton.elim j' j0
    subst hj0
    refine ⟨j0, ?_⟩
    change pt₁ β = x
    change pt₂ (g β) = f x at hj'
    rw [hg_pt] at hj'
    exact f.injective hj'

theorem bibd_fin2_exists_iff {α : Type*} (p : Fin 2 → α) (x : α) :
    (∃ j, p j = x) ↔ p ⟨0, by omega⟩ = x ∨ p ⟨1, by omega⟩ = x := by
  let j0 : Fin 2 := ⟨0, by omega⟩
  let j1 : Fin 2 := ⟨1, by omega⟩
  have hj : ∀ j : Fin 2, j = j0 ∨ j = j1 := by
    intro ⟨val, hval⟩
    interval_cases val
    · left; rfl
    · right; rfl
  constructor
  · rintro ⟨j, hjx⟩
    rcases hj j with rfl | rfl
    · left; exact hjx
    · right; exact hjx
  · rintro (h | h)
    · exact ⟨j0, h⟩
    · exact ⟨j1, h⟩

theorem bibd_sym2_mem_iff_f {α β : Type*} (f : α ≃ β) (a₁ b₁ x : α) (a₂ b₂ : β)
    (h : s(a₂, b₂) = s(f a₁, f b₁)) :
    (a₂ = f x ∨ b₂ = f x) ↔ (a₁ = x ∨ b₁ = x) := by
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [EmbeddingLike.apply_eq_iff_eq]
  · simp only [EmbeddingLike.apply_eq_iff_eq, or_comm]

theorem bibd_isomorphic_of_k_two {X₁ B₁ X₂ B₂ : Type*} [Finite B₁] [Finite B₂]
    {v b r lam : ℕ} (D₁ : BIBD X₁ B₁ v b r 2 lam) (D₂ : BIBD X₂ B₂ v b r 2 lam) :
    bibd_isomorphic D₁ D₂ := by
  have hv : v ≠ 0 := by
    have := D₁.incomplete
    omega
  have fx1 : Finite X₁ := Nat.finite_of_card_ne_zero (by rw [D₁.card_points]; exact hv)
  have fx2 : Finite X₂ := Nat.finite_of_card_ne_zero (by rw [D₂.card_points]; exact hv)
  have hX : Nonempty (X₁ ≃ X₂) := Finite.card_eq.mp (by rw [D₁.card_points, D₂.card_points])
  rcases hX with ⟨f⟩
  let j0 : Fin 2 := ⟨0, by omega⟩
  let j1 : Fin 2 := ⟨1, by omega⟩
  let pair₁ : B₁ → Sym2 X₁ := fun β => s(D₁.block_pts β j0, D₁.block_pts β j1)
  let pair₂ : B₂ → Sym2 X₂ := fun β => s(D₂.block_pts β j0, D₂.block_pts β j1)
  have hj : ∀ j : Fin 2, j = j0 ∨ j = j1 := by
    intro ⟨val, hval⟩
    interval_cases val
    · left; rfl
    · right; rfl
  have h_fib_eq₁ : ∀ (β : B₁) (x y : X₁), x ≠ y → (pair₁ β = s(x, y) ↔ (∃ j, D₁.block_pts β j = x) ∧ ∃ j', D₁.block_pts β j' = y) := by
    intro β x y hxy
    simp only [pair₁, Sym2.eq_iff]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · refine ⟨⟨j0, h0⟩, ⟨j1, h1⟩⟩
      · refine ⟨⟨j1, h1⟩, ⟨j0, h0⟩⟩
    · rintro ⟨⟨j, hjx⟩, ⟨j', hj'y⟩⟩
      rcases hj j with rfl | rfl <;> rcases hj j' with rfl | rfl
      · subst hjx hj'y; exact (hxy rfl).elim
      · left; exact ⟨hjx, hj'y⟩
      · right; exact ⟨hj'y, hjx⟩
      · subst hjx hj'y; exact (hxy rfl).elim
  have h_fib_eq₂ : ∀ (β : B₂) (x y : X₂), x ≠ y → (pair₂ β = s(x, y) ↔ (∃ j, D₂.block_pts β j = x) ∧ ∃ j', D₂.block_pts β j' = y) := by
    intro β x y hxy
    simp only [pair₂, Sym2.eq_iff]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · refine ⟨⟨j0, h0⟩, ⟨j1, h1⟩⟩
      · refine ⟨⟨j1, h1⟩, ⟨j0, h0⟩⟩
    · rintro ⟨⟨j, hjx⟩, ⟨j', hj'y⟩⟩
      rcases hj j with rfl | rfl <;> rcases hj j' with rfl | rfl
      · subst hjx hj'y; exact (hxy rfl).elim
      · left; exact ⟨hjx, hj'y⟩
      · right; exact ⟨hj'y, hjx⟩
      · subst hjx hj'y; exact (hxy rfl).elim
  have pair_not_diag₁ : ∀ β : B₁, ¬ (pair₁ β).IsDiag := by
    intro β
    rw [Sym2.mk_isDiag_iff]
    intro h
    have := D₁.block_inj β h
    revert this
    decide
  have pair_not_diag₂ : ∀ β : B₂, ¬ (pair₂ β).IsDiag := by
    intro β
    rw [Sym2.mk_isDiag_iff]
    intro h
    have := D₂.block_inj β h
    revert this
    decide
  have card_fib₁ : ∀ (p : Sym2 X₁), ¬ p.IsDiag → Nat.card { β : B₁ // pair₁ β = p } = lam := by
    intro p hp
    induction' p using Sym2.ind with x y
    rw [Sym2.mk_isDiag_iff] at hp
    have heq : { β : B₁ // pair₁ β = s(x, y) } ≃ { β : B₁ // (∃ j, D₁.block_pts β j = x) ∧ ∃ j', D₁.block_pts β j' = y } :=
      Equiv.subtypeEquivRight (fun β => h_fib_eq₁ β x y hp)
    rw [Nat.card_congr heq]
    exact D₁.balance hp
  have card_fib₂ : ∀ (p : Sym2 X₂), ¬ p.IsDiag → Nat.card { β : B₂ // pair₂ β = p } = lam := by
    intro p hp
    induction' p using Sym2.ind with x y
    rw [Sym2.mk_isDiag_iff] at hp
    have heq : { β : B₂ // pair₂ β = s(x, y) } ≃ { β : B₂ // (∃ j, D₂.block_pts β j = x) ∧ ∃ j', D₂.block_pts β j' = y } :=
      Equiv.subtypeEquivRight (fun β => h_fib_eq₂ β x y hp)
    rw [Nat.card_congr heq]
    exact D₂.balance hp
  let sym2_f : Sym2 X₁ ≃ Sym2 X₂ :=
    { toFun := Sym2.map f
      invFun := Sym2.map f.symm
      left_inv := fun p => by induction' p using Sym2.ind with x y; simp
      right_inv := fun p => by induction' p using Sym2.ind with x y; simp }
  have sym2_f_isDiag : ∀ p : Sym2 X₁, (sym2_f p).IsDiag ↔ p.IsDiag := by
    intro p
    induction' p using Sym2.ind with x y
    simp [sym2_f, Sym2.mk_isDiag_iff]
  have sym2_f_symm_isDiag : ∀ p : Sym2 X₂, (sym2_f.symm p).IsDiag ↔ p.IsDiag := by
    intro p
    have := sym2_f_isDiag (sym2_f.symm p)
    rw [sym2_f.apply_symm_apply] at this
    exact this.symm
  let pair_equiv : { p : Sym2 X₁ // ¬ p.IsDiag } ≃ { p : Sym2 X₂ // ¬ p.IsDiag } :=
    { toFun := fun ⟨p, hp⟩ => ⟨sym2_f p, by rwa [sym2_f_isDiag]⟩
      invFun := fun ⟨p, hp⟩ => ⟨sym2_f.symm p, by rwa [sym2_f_symm_isDiag]⟩
      left_inv := fun ⟨p, hp⟩ => Subtype.ext (sym2_f.symm_apply_apply p)
      right_inv := fun ⟨p, hp⟩ => Subtype.ext (sym2_f.apply_symm_apply p) }
  have fib_iso : ∀ P : { p : Sym2 X₁ // ¬ p.IsDiag },
      Nonempty ({ β : B₁ // pair₁ β = P.1 } ≃ { β : B₂ // pair₂ β = (pair_equiv P).1 }) := by
    intro P
    apply Finite.card_eq.mp
    rw [card_fib₁ P.1 P.2, card_fib₂ (pair_equiv P).1 (pair_equiv P).2]
  let e₁ : B₁ ≃ (P : { p : Sym2 X₁ // ¬ p.IsDiag }) × { β : B₁ // pair₁ β = P.1 } :=
    { toFun := fun β => ⟨⟨pair₁ β, pair_not_diag₁ β⟩, ⟨β, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun β => rfl
      right_inv := fun ⟨⟨p, hp⟩, ⟨β, hβ⟩⟩ => by
        dsimp at hβ
        subst hβ
        rfl }
  let e₂ : B₂ ≃ (P : { p : Sym2 X₂ // ¬ p.IsDiag }) × { β : B₂ // pair₂ β = P.1 } :=
    { toFun := fun β => ⟨⟨pair₂ β, pair_not_diag₂ β⟩, ⟨β, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun β => rfl
      right_inv := fun ⟨⟨p, hp⟩, ⟨β, hβ⟩⟩ => by
        dsimp at hβ
        subst hβ
        rfl }
  let e_sigma : ((P : { p : Sym2 X₁ // ¬ p.IsDiag }) × { β : B₁ // pair₁ β = P.1 }) ≃
      ((P : { p : Sym2 X₂ // ¬ p.IsDiag }) × { β : B₂ // pair₂ β = P.1 }) :=
    Equiv.sigmaCongr pair_equiv (fun P => (fib_iso P).some)
  let g : B₁ ≃ B₂ := e₁.trans (e_sigma.trans e₂.symm)
  have hg_pair : ∀ β : B₁, pair₂ (g β) = sym2_f (pair₁ β) := by
    intro β
    have this1 : (e_sigma (e₁ β)).1 = pair_equiv ⟨pair₁ β, pair_not_diag₁ β⟩ := rfl
    have he2 : (e₂ (g β)).1 = (e_sigma (e₁ β)).1 := by
      change (e₂ (e₂.symm (e_sigma (e₁ β)))).1 = (e_sigma (e₁ β)).1
      rw [e₂.apply_symm_apply]
    have := he2.trans this1
    exact congr_arg Subtype.val this
  refine ⟨f, g, fun β x => ?_⟩
  have hp : pair₂ (g β) = s(f (D₁.block_pts β j0), f (D₁.block_pts β j1)) := by
    rw [hg_pair β]
    rfl
  rw [bibd_fin2_exists_iff, bibd_fin2_exists_iff]
  exact (bibd_sym2_mem_iff_f f (D₁.block_pts β j0) (D₁.block_pts β j1) x (D₂.block_pts (g β) j0) (D₂.block_pts (g β) j1) hp).symm

theorem bibd_isomorphic_of_block_clique_graph_iso {X₁ B₁ X₂ B₂ : Type*} [Finite B₁] [Finite B₂]
    {v b r k lam : ℕ} (D₁ : BIBD X₁ B₁ v b r k lam) (D₂ : BIBD X₂ B₂ v b r k lam)
    (h : Nonempty (bibd_block_clique_graph D₁ ≃g bibd_block_clique_graph D₂)) :
    bibd_isomorphic D₁ D₂ := by
  rcases k with _ | _ | _ | k
  · exact bibd_isomorphic_of_k_zero D₁ D₂
  · exact bibd_isomorphic_of_k_one D₁ D₂
  · exact bibd_isomorphic_of_k_two D₁ D₂
  · exact bibd_isomorphic_of_block_clique_graph_iso_of_three_le D₁ D₂ (by omega) h
