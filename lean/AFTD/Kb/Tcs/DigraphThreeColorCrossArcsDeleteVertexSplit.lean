import AFTD.Prelude

/-!
# digraph_three_color_cross_arcs_delete_vertex_split

Topic: graphs   Node: d34720abfda4

Provenance: helper lemma. Arc decomposition for the exceptional-vertex reduction of OP-110.

The number of arcs crossing three vertex colors equals the number crossing among the vertices other than a distinguished vertex plus the numbers of crossing arcs entering and leaving that vertex.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem digraph_three_color_cross_arcs_delete_vertex_split
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (x : α) (col : α → Fin 3) :
    let S : Set α := {x}ᶜ
    let E : Digraph S := ⟨fun u v => D.Adj u.1 v.1⟩
    (∑ u : α, (Finset.univ.filter fun v => col v ≠ col u ∧ D.Adj u v).card) =
      (∑ u : S, (Finset.univ.filter fun v : S => col v.1 ≠ col u.1 ∧ E.Adj u v).card) +
      (Finset.univ.filter fun v => col v ≠ col x ∧ D.Adj x v).card +
      (Finset.univ.filter fun u => col u ≠ col x ∧ D.Adj u x).card := by
  classical
  let S : Set α := {x}ᶜ
  let E : Digraph S := ⟨fun u v => D.Adj u.1 v.1⟩
  let F : α → α → ℕ := fun u v => if col v ≠ col u ∧ D.Adj u v then 1 else 0
  let U : Finset α := Finset.univ.erase x
  have hsub (f : α → ℕ) : (∑ u : S, f u.1) = ∑ u ∈ U, f u := by
    symm
    apply Finset.sum_subtype U
    intro v
    simp [U,S]
  have hsplit (f : α → ℕ) : (∑ u : α, f u) = (∑ u ∈ U, f u) + f x := by
    symm
    exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ x)
  have hrest : (∑ u : S, (Finset.univ.filter fun v : S => col v.1 ≠ col u.1 ∧ E.Adj u v).card) =
      ∑ u ∈ U, ∑ v ∈ U, F u v := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    change (∑ u : S, ∑ v : S, F u.1 v.1) = _
    calc
      (∑ u : S, ∑ v : S, F u.1 v.1) = ∑ u : S, ∑ v ∈ U, F u.1 v := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hsub (F u.1)
      _ = ∑ u ∈ U, ∑ v ∈ U, F u v := hsub (fun u => ∑ v ∈ U, F u v)
  have hall : (∑ u : α, (Finset.univ.filter fun v => col v ≠ col u ∧ D.Adj u v).card) =
      ∑ u : α, ∑ v : α, F u v := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rfl
  have hout : (Finset.univ.filter fun v => col v ≠ col x ∧ D.Adj x v).card =
      ∑ v : α, F x v := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rfl
  have hin : (Finset.univ.filter fun u => col u ≠ col x ∧ D.Adj u x).card =
      ∑ u ∈ U, F u x := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hzero : F x x = 0 := by simp [F]
    have h := hsplit (fun u => F u x)
    rw [hzero, Nat.add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [F, ne_comm]
  have hdouble : (∑ u : α, ∑ v : α, F u v) =
      (∑ u ∈ U, ∑ v ∈ U, F u v) + (∑ v : α, F x v) + (∑ u ∈ U, F u x) := by
    rw [hsplit (fun u => ∑ v : α, F u v)]
    have heach : (∑ u ∈ U, ∑ v : α, F u v) =
        (∑ u ∈ U, ∑ v ∈ U, F u v) + ∑ u ∈ U, F u x := by
      simp_rw [hsplit (F _)]
      rw [Finset.sum_add_distrib]
    rw [heach]
    omega
  change _ = _ + _ + _
  rw [hall,hrest,hout,hin]
  exact hdouble
