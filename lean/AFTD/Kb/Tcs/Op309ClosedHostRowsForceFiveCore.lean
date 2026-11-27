import AFTD.Prelude
import AFTD.Kb.Tcs.Op309GraphFourDegenerate

/-!
# op309_closed_host_rows_force_five_core

Topic: graphs   Node: be0a808f2424

Provenance: helper lemma. Pairing-independent pure-host five-core argument for OP-309, experiments 42690, 42839 and 42840.

A nonempty closed family of path classes whose two three-class host rows intersect only in the given class, with at most one class per path in each row, forces a five-core and hence is not four-degenerate.
-/

theorem op309_closed_host_rows_force_five_core
    {P H A : Type*} [Fintype P] [DecidableEq P] [DecidableEq H] [DecidableEq A] [Nonempty P]
    (Q : SimpleGraph A) (q : P × Fin 2 → A) (hq : Function.Injective q)
    (rows : H → Finset (P × Fin 2)) (host : (P × Fin 2) → Fin 2 → H)
    (hcard : ∀ h, (rows h).card = 3)
    (hmem : ∀ x j, x ∈ rows (host x j))
    (hpath : ∀ h x y, x ∈ rows h → y ∈ rows h → x.1 = y.1 → x = y)
    (hinter : ∀ x y, y ∈ rows (host x 0) → y ∈ rows (host x 1) → y = x)
    (hclique : ∀ h x y, x ∈ rows h → y ∈ rows h → x ≠ y → Q.Adj (q x) (q y))
    (hpartner : ∀ p i, Q.Adj (q (p,i)) (q (p,1-i))) :
    ¬ op309_graph_four_degenerate Q := by
  classical
  intro hdeg
  let S : Finset A := Finset.univ.image q
  obtain ⟨p⟩ := ‹Nonempty P›
  have hS : S.Nonempty := ⟨q (p,0), Finset.mem_image.mpr ⟨(p,0), Finset.mem_univ _, rfl⟩⟩
  obtain ⟨v,hv,T,hT,hcover⟩ := hdeg S hS
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
  let A0 := (rows (host x 0)).erase x
  let A1 := (rows (host x 1)).erase x
  let other : P × Fin 2 := (x.1, 1-x.2)
  have hother : other ≠ x := by
    rcases x with ⟨p,i⟩
    fin_cases i <;> simp [other]
  have hc0 : A0.card = 2 := by simp [A0, hmem, hcard]
  have hc1 : A1.card = 2 := by simp [A1, hmem, hcard]
  have hd : Disjoint A0 A1 := by
    apply Finset.disjoint_left.mpr
    intro y hy0 hy1
    simp only [A0, Finset.mem_erase] at hy0
    simp only [A1, Finset.mem_erase] at hy1
    exact hy0.1 (hinter x y hy0.2 hy1.2)
  have hn0 : other ∉ A0 := by
    intro ho
    have hr : other ∈ rows (host x 0) := (Finset.mem_erase.mp ho).2
    exact hother (hpath _ other x hr (hmem x 0) rfl)
  have hn1 : other ∉ A1 := by
    intro ho
    have hr : other ∈ rows (host x 1) := (Finset.mem_erase.mp ho).2
    exact hother (hpath _ other x hr (hmem x 1) rfl)
  let N : Finset (P × Fin 2) := insert other (A0 ∪ A1)
  have hNcard : N.card = 5 := by
    have hn : other ∉ A0 ∪ A1 := by simp [hn0,hn1]
    simp [N, hn, Finset.card_union_of_disjoint hd, hc0, hc1]
  have hNadj : ∀ y ∈ N, Q.Adj (q x) (q y) := by
    intro y hy
    simp only [N, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · rcases x with ⟨p,i⟩
      exact hpartner p i
    · have hh := Finset.mem_erase.mp hy
      exact hclique _ x y (hmem x 0) hh.2 (Ne.symm hh.1)
    · have hh := Finset.mem_erase.mp hy
      exact hclique _ x y (hmem x 1) hh.2 (Ne.symm hh.1)
  have hsub : N.image q ⊆ T := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    apply hcover (q y)
    · exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩
    · exact hNadj y hy
  have hle := Finset.card_le_card hsub
  have himage : (N.image q).card = N.card := Finset.card_image_iff.mpr (fun _ _ _ _ h => hq h)
  omega
