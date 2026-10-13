import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentMinRank
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.TournamentExistsFamilyLengthEqInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphFlipByMatrix
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic

/-!
# tournament_min_rank_le_inversion_number

Topic: graphs   Node: 8bea455ed77c

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), inequality (1.2), quoting an earlier paper (the sum of the rank-one matrices 1_X 1_Xᵀ over a decycling family is a decycling matrix of rank at most the family size).

For a finite tournament D: tmr(D) ≤ inv(D).
-/

theorem tournament_min_rank_le_inversion_number (V : Type) [Fintype V] (D : Digraph V)
    (h : digraph_is_tournament D) :
    tournament_min_rank D ≤ digraph_inversion_number D := by
  classical
  obtain ⟨Xs, hXl, hXa⟩ := tournament_exists_family_length_eq_inversion_number V D h
  let A : {n : ℕ} → (Fin n → Set V) → Matrix V (Fin n) (ZMod 2) :=
    fun X x i => if x ∈ X i then 1 else 0
  let N : Set V → Matrix V V (ZMod 2) :=
    fun X x y => (if x ∈ X then 1 else 0) * (if y ∈ X then 1 else 0)
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have two : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have flip_add : ∀ (E : Digraph V) (P M : Matrix V V (ZMod 2)), (∀ x y, P y x = P x y) →
      digraph_flip_by_matrix (digraph_flip_by_matrix E P) M =
        digraph_flip_by_matrix E (P + M) := by
    intro E P M hP
    ext x y
    simp only [digraph_flip_by_matrix, Matrix.add_apply, hP x y]
    rcases two (P x y) with ha | ha <;> rcases two (M x y) with hb | hb <;>
      simp [ha, hb, h11]
  have hN : ∀ (E : Digraph V) (X : Set V), digraph_invert E X = digraph_flip_by_matrix E (N X) := by
    intro E X
    ext x y
    simp only [digraph_flip_by_matrix, digraph_invert, N]
    by_cases hx : x ∈ X <;> by_cases hy : y ∈ X <;> simp [hx, hy]
  have key : ∀ (n : ℕ) (X : Fin n → Set V) (E : Digraph V),
      digraph_flip_by_matrix E (A X * (A X).transpose) = (List.ofFn X).foldl digraph_invert E := by
    intro n
    induction n with
    | zero =>
      intro X E
      ext x y
      simp [digraph_flip_by_matrix, Matrix.mul_apply]
    | succ n ih =>
      intro X E
      rw [List.ofFn_succ, List.foldl_cons, ← ih (fun i => X i.succ), hN, flip_add]
      · congr 1
        ext x y
        simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
        rfl
      · intro x y
        simp only [N]
        ring
  have hsymm : (A Xs.get * (A Xs.get).transpose).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hac : digraph_is_acyclic (digraph_flip_by_matrix D (A Xs.get * (A Xs.get).transpose)) := by
    rw [key, List.ofFn_get]
    exact hXa
  calc tournament_min_rank D ≤ (A Xs.get * (A Xs.get).transpose).rank :=
        Nat.sInf_le ⟨_, hsymm, hac, rfl⟩
    _ ≤ (A Xs.get).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin Xs.length) := Matrix.rank_le_card_width _
    _ = digraph_inversion_number D := by simp [hXl]
