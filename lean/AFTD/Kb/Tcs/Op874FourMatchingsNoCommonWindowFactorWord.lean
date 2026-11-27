import AFTD.Prelude
import AFTD.Kb.Tcs.Op874CyclePaletteKernel
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC01
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC02
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC20
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC21a
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC21b
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC21c
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC23a
import AFTD.Kb.Tcs.Op874FourMatchingsWindowCubeC23b
import AFTD.Kb.Tcs.C

/-!
# op874_four_matchings_no_common_window_factor_word

Topic: graphs   Node: b137f22dac94

Provenance: helper lemma. Joint color/port coordination obstruction for the OP-874 campaign, https://arxiv.org/abs/2610.41950.

For four displayed saturated matchings of the same 8- and 12-cycle factor and bit assignment, no single high factor-coloring supports compatible exact-owner local states for all four while satisfying the two forced four-window requirements. Each matching separately admits such a coloring in the finite experiments.
-/

namespace IN1204

def third (a b : Fin 4) : Fin 4 := if 0 ≠ a ∧ 0 ≠ b then 0 else if 1 ≠ a ∧ 1 ≠ b then 1 else 2

def perm (a b c d : Fin 4) : Fin 4 → Fin 4 := fun z =>
  if z = a then 0 else if z = b then 1
  else if z = (if c = a then (if d = b then third a b else d) else c) then 2 else 3

theorem perm_ok : ∀ a b c d : Fin 4, a ≠ b → b ≠ c → c ≠ d →
    (∀ z w, perm a b c d z = perm a b c d w → z = w) ∧ perm a b c d a = 0 ∧ perm a b c d b = 1 ∧
    ((perm a b c d c = 0 ∧ (perm a b c d d = 1 ∨ perm a b c d d = 2)) ∨
     (perm a b c d c = 2 ∧ (perm a b c d d = 0 ∨ perm a b c d d = 1 ∨ perm a b c d d = 3))) := by
  unfold perm third; decide

theorem ne_of_vertex (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (hP : P f h)
    (v : Fin 20) (ha : (inc 0 v 0).val < 20) (hb : (inc 0 v 1).val < 20) :
    f (e20 (inc 0 v 0)) ≠ f (e20 (inc 0 v 1)) := by
  intro e
  apply (hP.1 0 v 0 1 (by decide)).1
  rw [color_lt f 0 _ ha, color_lt f 0 _ hb, e]

theorem sym (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (hP : P f h) :
    ∃ f' h', P f' h' ∧ f' 10 = 0 ∧ f' 11 = 1 ∧
      ((f' 12 = 0 ∧ (f' 13 = 1 ∨ f' 13 = 2)) ∨ (f' 12 = 2 ∧ (f' 13 = 0 ∨ f' 13 = 1 ∨ f' 13 = 3))) := by
  have d1 : f 10 ≠ f 11 := ne_of_vertex f h hP 11 (by decide) (by decide)
  have d2 : f 11 ≠ f 12 := ne_of_vertex f h hP 12 (by decide) (by decide)
  have d3 : f 12 ≠ f 13 := ne_of_vertex f h hP 13 (by decide) (by decide)
  obtain ⟨σinj, s0, s1, s23⟩ := perm_ok (f 10) (f 11) (f 12) (f 13) d1 d2 d3
  set σ := perm (f 10) (f 11) (f 12) (f 13) with hσ
  have σi : Function.Injective σ := fun z w e => σinj z w e
  have σs : Function.Surjective σ := Finite.surjective_of_injective σi
  let τ : Fin 6 → Fin 6 := fun x => if hx : 2 ≤ x.val then c2 (σ ⟨x.val - 2, by omega⟩) else x
  have τc : ∀ c : Fin 4, τ (c2 c) = c2 (σ c) := by
    intro c
    simp only [τ, c2, show 2 ≤ c.val + 2 by omega, dite_true, Nat.add_sub_cancel]
  have τlo : ∀ x : Fin 6, x.val < 2 → τ x = x := by
    intro x hx
    simp only [τ, dif_neg (show ¬ 2 ≤ x.val by omega)]
  have τi : Function.Injective τ := by
    intro x y hxy
    by_cases hx : 2 ≤ x.val <;> by_cases hy : 2 ≤ y.val
    · have := congrArg Fin.val hxy
      simp only [τ, dif_pos hx, dif_pos hy, c2] at this
      have e2 := σi (a₁ := ⟨x.val - 2, by omega⟩) (a₂ := ⟨y.val - 2, by omega⟩) (Fin.ext (by omega))
      have e3 := congrArg Fin.val e2
      simp only at e3
      exact Fin.ext (by omega)
    · have := congrArg Fin.val hxy
      simp only [τ, dif_pos hx, dif_neg hy, c2] at this
      omega
    · have := congrArg Fin.val hxy
      simp only [τ, dif_neg hx, dif_pos hy, c2] at this
      omega
    · simpa [τ, dif_neg hx, dif_neg hy] using hxy
  have τcol : ∀ q e, color (fun e => σ (f e)) q e = τ (color f q e) := by
    intro q e
    by_cases he : e.val < 20
    · rw [color_lt _ q e he, color_lt _ q e he, τc]
    · rw [color_ge _ q e he, color_ge _ q e he, τlo]
      unfold mcol; split <;> decide
  have τopp : ∀ b : Bool, τ (if b then 0 else 1) = (if b then 0 else 1) := by
    intro b; apply τlo; split <;> decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  refine ⟨fun e => σ (f e), fun q v e => τ (h q v e), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, s0, s1, s23⟩
  · intro q v i j hij
    rw [τcol, τcol]
    exact ⟨τi.ne (h1 q v i j hij).1, τi.ne (h1 q v i j hij).2⟩
  · intro q v i j
    rw [τcol]
    exact τi.ne (h2 q v i j)
  · intro q e i j hi hj
    exact τi.ne (h3 q e i j hi hj)
  · intro q e he ⟨a, b⟩
    rw [← τopp] at a b
    exact h4 q e he ⟨τi a, τi b⟩
  · intro k
    obtain ⟨k', rfl⟩ := σs k
    obtain ⟨j, hj⟩ := h5 k'
    exact ⟨j, by simp only [hj]⟩
  · intro k
    obtain ⟨k', rfl⟩ := σs k
    obtain ⟨j, hj⟩ := h6 k'
    exact ⟨j, by simp only [hj]⟩

end IN1204

theorem op874_four_matchings_no_common_window_factor_word :
    let L : Fin 4 → Fin 30 → Fin 20 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,5,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,5,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16]]
    let R : Fin 4 → Fin 30 → Fin 20 := ![![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,6,8,7,11,15,13,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,6,11,7,8,13,15,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,8,5,7,11,15,13,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,11,5,7,8,15,13,18,17,19]]
    let inc : Fin 4 → Fin 20 → Fin 3 → Fin 30 := ![![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,24],![5,6,21],![6,7,23],![8,19,22],![8,9,25],![9,10,26],![10,11,24],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,24],![5,6,21],![6,7,23],![8,19,24],![8,9,25],![9,10,26],![10,11,22],![11,12,27],![12,13,25],![13,14,28],![14,15,26],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,22],![5,6,24],![6,7,23],![8,19,21],![8,9,25],![9,10,26],![10,11,24],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,22],![5,6,24],![6,7,23],![8,19,24],![8,9,25],![9,10,26],![10,11,21],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,28],![17,18,27],![18,19,29]]]
    let bit : Fin 20 → Bool := ![true,false,false,true,true,false,false,true,false,false,false,false,true,false,true,false,true,true,true,true]
    ¬ ∃ (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6),
      let color : Fin 4 → Fin 30 → Fin 6 := fun q e =>
        if he : e.val < 20 then ⟨(f ⟨e.val, he⟩).val + 2, by omega⟩
        else if bit (L q e) then 1 else 0
      (∀ q : Fin 4, ∀ v : Fin 20, ∀ i j : Fin 3,
        i ≠ j → color q (inc q v i) ≠ color q (inc q v j) ∧ h q v (inc q v i) ≠ h q v (inc q v j)) ∧
      (∀ q : Fin 4, ∀ v : Fin 20, ∀ i j : Fin 3, h q v (inc q v i) ≠ color q (inc q v j)) ∧
      (∀ q : Fin 4, ∀ e : Fin 30, ∀ i j : Fin 3,
        inc q (L q e) i ≠ e → inc q (R q e) j ≠ e →
        h q (L q e) (inc q (L q e) i) ≠ h q (R q e) (inc q (R q e) j)) ∧
      (∀ q : Fin 4, ∀ e : Fin 30, 20 ≤ e.val →
        ¬ (h q (L q e) e = (if bit (L q e) then 0 else 1) ∧
           h q (R q e) e = (if bit (R q e) then 0 else 1))) ∧
      (∀ k : Fin 4, ∃ j : Fin 6, f ((![10,11,12,13,14,15] : Fin 6 → Fin 20) j) = k) ∧
      (∀ k : Fin 4, ∃ j : Fin 6, f ((![11,12,13,14,15,16] : Fin 6 → Fin 20) j) = k) := by
  intro L R inc bit
  rintro ⟨f, h, hP⟩
  obtain ⟨f', h', hP', u10, u11, hc⟩ := IN1204.sym f h hP
  rcases hc with ⟨u12, u13 | u13⟩ | ⟨u12, u13 | u13 | u13⟩
  · exact op874_four_matchings_window_cube_c01 ⟨f', h', hP', u10, u11, u12, u13⟩
  · exact op874_four_matchings_window_cube_c02 ⟨f', h', hP', u10, u11, u12, u13⟩
  · exact op874_four_matchings_window_cube_c20 ⟨f', h', hP', u10, u11, u12, u13⟩
  · by_cases u8 : f' 8 = 3
    · by_cases u5 : f' 5 = 3
      · exact op874_four_matchings_window_cube_c21b ⟨f', h', hP', u10, u11, u12, u13, u8, u5⟩
      · exact op874_four_matchings_window_cube_c21c ⟨f', h', hP', u10, u11, u12, u13, u8, u5⟩
    · exact op874_four_matchings_window_cube_c21a ⟨f', h', hP', u10, u11, u12, u13, u8⟩
  · by_cases u15 : f' 15 = 3
    · exact op874_four_matchings_window_cube_c23a ⟨f', h', hP', u10, u11, u12, u13, u15⟩
    · exact op874_four_matchings_window_cube_c23b ⟨f', h', hP', u10, u11, u12, u13, u15⟩
