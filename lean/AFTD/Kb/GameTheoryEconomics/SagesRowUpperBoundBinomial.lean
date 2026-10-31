import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SagesRowOtherThan
import AFTD.Kb.GameTheoryEconomics.SagesRowEdgeSet
import AFTD.Kb.GameTheoryEconomics.SagesRowPairProtocol
import AFTD.Kb.GameTheoryEconomics.RowProblemSolvable
import AFTD.Kb.GameTheoryEconomics.RowProtocolSolves
import AFTD.Kb.GameTheoryEconomics.RowViewOfSage
import AFTD.Kb.GameTheoryEconomics.RowView
import AFTD.Kb.GameTheoryEconomics.RowMultiset
import AFTD.Kb.GameTheoryEconomics.RowLocalView

/-!
# sages_row_upper_bound_binomial

Topic: combinatorial_games   Node: 7c861bba14ea

Provenance: helper lemma. arXiv:2610.33032 Theorem 3 -- Sages and Their Anonymous Slips

For every integer S ≥ 3, the anonymous-slip puzzle for S sages in a row with unlabeled seats can be solved using Nat.choose S 2 symbols.
-/

/-- `{u, v}` is an edge of the row seating `π`: two seats in a row hold `u` and `v`. -/
def srbx_E {S : ℕ} (π : Equiv.Perm (Fin S)) (u v : Fin S) : Prop :=
  ∃ k k' : Fin S, k'.val = k.val + 1 ∧ ({u, v} : Finset (Fin S)) = {π k, π k'}

theorem srbx_pair_eq {S : ℕ} {u v x y : Fin S} (hxy : x ≠ y)
    (h : ({u, v} : Finset (Fin S)) = {x, y}) : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have hu : u ∈ ({x, y} : Finset (Fin S)) := h ▸ by simp
  have hv : v ∈ ({x, y} : Finset (Fin S)) := h ▸ by simp
  have hx : x ∈ ({u, v} : Finset (Fin S)) := h.symm ▸ by simp
  have hy : y ∈ ({u, v} : Finset (Fin S)) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hx hy
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (hxy (by rcases hy with h | h <;> rw [h] <;> simp [hu, hv])).elim
  · exact Or.inl ⟨hu, hv⟩
  · exact Or.inr ⟨hu, hv⟩
  · exact (hxy (by rcases hx with h | h <;> rw [h] <;> simp [hu, hv])).elim

/-- The neighbours of the seat `c` in the row. -/
theorem srbx_nbr {S : ℕ} (π : Equiv.Perm (Fin S)) {u v : Fin S} (h : srbx_E π u v) (c : Fin S)
    (hu : u = π c) :
    (∃ c' : Fin S, c'.val = c.val + 1 ∧ v = π c') ∨ (∃ c' : Fin S, c'.val + 1 = c.val ∧ v = π c') := by
  obtain ⟨k, k', hk, he⟩ := h
  have hne : π k ≠ π k' := fun h => by
    have := congrArg Fin.val (π.injective h); omega
  rcases srbx_pair_eq hne he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : c = k := π.injective (hu.symm.trans h1)
    subst this
    exact Or.inl ⟨k', hk, h2⟩
  · have : c = k' := π.injective (hu.symm.trans h1)
    subst this
    exact Or.inr ⟨k, hk.symm, h2⟩

/-- Following the row to the right from two matching seats. -/
theorem srbx_right {S : ℕ} (π₁ π₂ : Equiv.Perm (Fin S))
    (hE : ∀ u v, srbx_E π₁ u v → srbx_E π₂ u v) (a b : Fin S) (h0 : π₁ a = π₂ b)
    (h1 : ∀ a' : Fin S, a'.val = a.val + 1 → ∃ b' : Fin S, b'.val = b.val + 1 ∧ π₁ a' = π₂ b') :
    ∀ j : ℕ, ∀ i₁ : Fin S, i₁.val = a.val + j → ∃ i₂ : Fin S, i₂.val = b.val + j ∧ π₁ i₁ = π₂ i₂ := by
  have key : ∀ j : ℕ,
      (∀ i₁ : Fin S, i₁.val = a.val + j → ∃ i₂ : Fin S, i₂.val = b.val + j ∧ π₁ i₁ = π₂ i₂) ∧
      (∀ i₁ : Fin S, i₁.val = a.val + (j + 1) →
        ∃ i₂ : Fin S, i₂.val = b.val + (j + 1) ∧ π₁ i₁ = π₂ i₂) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun i₁ hi => ⟨b, rfl, ?_⟩, fun i₁ hi => h1 i₁ hi⟩
      rw [show i₁ = a from Fin.ext hi, h0]
    | succ j ih =>
      refine ⟨ih.2, fun i₁ hi => ?_⟩
      obtain ⟨q1, hq1, e1⟩ := ih.2 ⟨a.val + (j + 1), by omega⟩ rfl
      obtain ⟨q0, hq0, e0⟩ := ih.1 ⟨a.val + j, by omega⟩ rfl
      have hE1 : srbx_E π₁ (π₁ ⟨a.val + (j + 1), by omega⟩) (π₁ i₁) :=
        ⟨⟨a.val + (j + 1), by omega⟩, i₁, by simp only [Fin.val_mk]; omega, rfl⟩
      rcases srbx_nbr π₂ (hE _ _ hE1) q1 e1 with ⟨c', hc', hv⟩ | ⟨c', hc', hv⟩
      · exact ⟨c', by omega, hv⟩
      · exfalso
        have hcq : c' = q0 := Fin.ext (by omega)
        rw [hcq, ← e0] at hv
        have := congrArg Fin.val (π₁.injective hv)
        simp only [Fin.val_mk] at this
        omega
  intro j i₁ hi
  exact (key j).1 i₁ hi

/-- The seating read from right to left. -/
theorem srbx_E_rev {S : ℕ} (π : Equiv.Perm (Fin S)) {u v : Fin S} (h : srbx_E π u v) :
    srbx_E (Fin.revPerm.trans π) u v := by
  obtain ⟨k, k', hk, he⟩ := h
  refine ⟨k'.rev, k.rev, ?_, ?_⟩
  · simp only [Fin.val_rev]; have := k'.isLt; omega
  · rw [he, Equiv.trans_apply, Equiv.trans_apply, Fin.revPerm_apply, Fin.revPerm_apply,
      Fin.rev_rev, Fin.rev_rev, Finset.pair_comm]

theorem srbx_rev_rev {S : ℕ} (π : Equiv.Perm (Fin S)) :
    Fin.revPerm.trans (Fin.revPerm.trans π) = π := by
  ext i; simp

theorem srbx_eval_lt {S : ℕ} (hS : 2 ≤ S) (π : Equiv.Perm (Fin S)) (i : Fin S) (hi : i.val + 1 < S) :
    (sages_row_pair_protocol hS (rowView hS π i)).val = {π i, π ⟨i.val + 1, hi⟩} := by
  have hne : π ⟨i.val + 1, hi⟩ ≠ π i := fun h => by
    have := congrArg Fin.val (π.injective h); simp only [Fin.val_mk] at this; omega
  have hl : ¬ i.val = S - 1 := by omega
  simp only [rowView]
  rw [dif_neg hl]
  simp [sages_row_pair_protocol, hne]

theorem srbx_eval_last {S : ℕ} (hS : 2 ≤ S) (π : Equiv.Perm (Fin S)) (i : Fin S) (hi : i.val = S - 1) :
    (sages_row_pair_protocol hS (rowView hS π i)).val = {π i, π ⟨i.val - 1, by omega⟩} := by
  have hne : π ⟨i.val - 1, by omega⟩ ≠ π i := fun h => by
    have := congrArg Fin.val (π.injective h); simp only [Fin.val_mk] at this; omega
  have h0 : ¬ i.val = 0 := by omega
  simp only [rowView]
  rw [dif_pos hi, dif_neg h0]
  simp [sages_row_pair_protocol, hne]

theorem srbx_E_iff {S : ℕ} (hS : 2 ≤ S) (π : Equiv.Perm (Fin S)) (u v : Fin S) :
    srbx_E π u v ↔ ∃ i, (sages_row_pair_protocol hS (rowView hS π i)).val = {u, v} := by
  constructor
  · rintro ⟨k, k', hk, he⟩
    refine ⟨k, ?_⟩
    rw [srbx_eval_lt hS π k (by omega), he]
    rw [show (⟨k.val + 1, by omega⟩ : Fin S) = k' from Fin.ext hk.symm]
  · rintro ⟨i, hi⟩
    by_cases h : i.val + 1 < S
    · rw [srbx_eval_lt hS π i h] at hi
      exact ⟨i, ⟨i.val + 1, h⟩, rfl, hi.symm⟩
    · rw [srbx_eval_last hS π i (by omega), Finset.pair_comm] at hi
      exact ⟨⟨i.val - 1, by omega⟩, i, by simp only [Fin.val_mk]; omega, hi.symm⟩

theorem srbx_view_right {S : ℕ} (hS : 2 ≤ S) (π₁ π₂ : Equiv.Perm (Fin S)) (a b : Fin S)
    (hv : rowView hS π₁ a = rowView hS π₂ b) :
    ∀ a' : Fin S, a'.val = a.val + 1 → ∃ b' : Fin S, b'.val = b.val + 1 ∧ π₁ a' = π₂ b' := by
  intro a' ha'
  have h3 := congrArg (fun v => v.2.2) hv
  simp only [rowView] at h3
  rw [dif_neg (by omega : ¬ a.val = S - 1)] at h3
  by_cases hB : b.val = S - 1
  · rw [dif_pos hB] at h3; exact absurd h3 (by simp)
  · rw [dif_neg hB] at h3
    refine ⟨⟨b.val + 1, by omega⟩, rfl, ?_⟩
    rw [← Option.some.inj h3]
    exact congrArg π₁ (Fin.ext ha')

theorem srbx_view_left {S : ℕ} (hS : 2 ≤ S) (π₁ π₂ : Equiv.Perm (Fin S)) (a b : Fin S)
    (hv : rowView hS π₁ a = rowView hS π₂ b) :
    ∀ a' : Fin S, a'.val + 1 = a.val → ∃ b' : Fin S, b'.val + 1 = b.val ∧ π₁ a' = π₂ b' := by
  intro a' ha'
  have h3 := congrArg (fun v => v.2.1) hv
  simp only [rowView] at h3
  rw [dif_neg (by omega : ¬ a.val = 0)] at h3
  by_cases hB : b.val = 0
  · rw [dif_pos hB] at h3; exact absurd h3 (by simp)
  · rw [dif_neg hB] at h3
    refine ⟨⟨b.val - 1, by omega⟩, by simp only [Fin.val_mk]; omega, ?_⟩
    rw [← Option.some.inj h3]
    exact congrArg π₁ (Fin.ext (by simp only [Fin.val_mk]; omega))

theorem srbx_solves {S : ℕ} (hS : 3 ≤ S) (hS2 : 2 ≤ S) :
    RowProtocolSolves S hS2 (sages_row_pair_protocol hS2) := by
  intro x π₁ π₂ hv hm
  unfold rowViewOfSage at hv
  set a := π₁.symm x
  set b := π₂.symm x
  have hE : ∀ (σ₁ σ₂ : Equiv.Perm (Fin S)),
      rowMultiset hS2 (sages_row_pair_protocol hS2) σ₁ = rowMultiset hS2 (sages_row_pair_protocol hS2) σ₂ →
      ∀ u v, srbx_E σ₁ u v → srbx_E σ₂ u v := by
    intro σ₁ σ₂ h u v huv
    obtain ⟨i, hi⟩ := (srbx_E_iff hS2 σ₁ u v).1 huv
    have hmem : sages_row_pair_protocol hS2 (rowView hS2 σ₁ i) ∈
        rowMultiset hS2 (sages_row_pair_protocol hS2) σ₂ := by
      rw [← h]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    obtain ⟨i₂, -, hi₂⟩ := Multiset.mem_map.1 hmem
    exact (srbx_E_iff hS2 σ₂ u v).2 ⟨i₂, by rw [hi₂, hi]⟩
  have hE12 := hE π₁ π₂ hm
  have hE21 := hE π₂ π₁ hm.symm
  have h0 : π₁ a = π₂ b := by simp [a, b]
  have R12 := srbx_right π₁ π₂ hE12 a b h0 (srbx_view_right hS2 π₁ π₂ a b hv)
  have R21 := srbx_right π₂ π₁ hE21 b a h0.symm (srbx_view_right hS2 π₂ π₁ b a hv.symm)
  have hab : a.val = b.val := by
    obtain ⟨i₂, hi₂, -⟩ := R12 (S - 1 - a.val) ⟨S - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    obtain ⟨i₁, hi₁, -⟩ := R21 (S - 1 - b.val) ⟨S - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    have := i₁.isLt; have := i₂.isLt
    omega
  -- the reversed seatings
  have hEr : ∀ u v, srbx_E (Fin.revPerm.trans π₁) u v → srbx_E (Fin.revPerm.trans π₂) u v := by
    intro u v h
    have h' := srbx_E_rev _ h
    rw [srbx_rev_rev] at h'
    exact srbx_E_rev _ (hE12 u v h')
  have hr0 : (Fin.revPerm.trans π₁) a.rev = (Fin.revPerm.trans π₂) b.rev := by
    simp [h0]
  have hr1 : ∀ a' : Fin S, a'.val = a.rev.val + 1 →
      ∃ b' : Fin S, b'.val = b.rev.val + 1 ∧ (Fin.revPerm.trans π₁) a' = (Fin.revPerm.trans π₂) b' := by
    intro a' ha'
    have := a.isLt; have := a'.isLt; have := b.isLt
    obtain ⟨b', hb', e⟩ := srbx_view_left hS2 π₁ π₂ a b hv a'.rev (by simp only [Fin.val_rev] at ha' ⊢; omega)
    refine ⟨b'.rev, by simp only [Fin.val_rev]; omega, ?_⟩
    simp [e]
  have Rr := srbx_right _ _ hEr a.rev b.rev hr0 hr1
  have := b.isLt
  apply Equiv.ext
  intro i
  by_cases hi : a.val ≤ i.val
  · obtain ⟨i₂, hi₂, e⟩ := R12 (i.val - a.val) i (by omega)
    rw [e, show i₂ = i from Fin.ext (by omega)]
  · obtain ⟨i₂, hi₂, e⟩ := Rr (a.val - i.val) i.rev (by simp only [Fin.val_rev]; omega)
    have hi₂' : i₂ = i.rev := Fin.ext (by simp only [Fin.val_rev] at hi₂ ⊢; omega)
    rw [hi₂'] at e
    simpa using e

/-- Universal upper bound of Nat.choose S 2 symbols for S sages in a row with unlabeled seats. -/
theorem sages_row_upper_bound_binomial (S : ℕ) (hS : 3 ≤ S) :
    RowProblemSolvable S (Nat.choose S 2) (by omega) := by
  have hS2 : 2 ≤ S := by omega
  have hc : Fintype.card {s : Finset (Fin S) // s.card = 2} = Nat.choose S 2 := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨fun v => e (sages_row_pair_protocol hS2 v), ?_⟩
  intro x π₁ π₂ hv hm
  apply srbx_solves hS hS2 x π₁ π₂ hv
  have hmap : ∀ π, rowMultiset hS2 (fun v => e (sages_row_pair_protocol hS2 v)) π =
      (rowMultiset hS2 (sages_row_pair_protocol hS2) π).map e := by
    intro π; simp [rowMultiset, Multiset.map_map, Function.comp_def]
  rw [hmap, hmap] at hm
  exact Multiset.map_injective e.injective hm
