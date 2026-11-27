import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FourSquaresOwnershipCountObstruction
import AFTD.Kb.Tcs.Op874OpenFourSquareRetainedMatchingOwners
import AFTD.Kb.Tcs.Op874OpenFourSquareMiddleMatchingOwnerBounds
import AFTD.Kb.Tcs.Op874OpenFourSquareOuterMatchingOwnerBounds
import AFTD.Kb.Tcs.CycleMatchingLowColor

/-!
# op874_open_four_square_global_pair_local_obstruction

Topic: graphs   Node: 6f00c02164e8

Provenance: helper lemma. OP-874; opened four-square block, experiments 41907 and 41910. Experiment 41917 checks all four independent choices of the opened port bits.

For the displayed four-square block with its eighth matching edge opened into two ports with arbitrary bits, no assignment of external and hidden colors satisfies the local six-color constraints, exact matching ownership on the seven retained internal matching edges, and one global high pair on unselected factor edges. No ownership or cross-interface condition is imposed at the remote port ends.
-/

theorem op874_open_four_square_global_pair_local_obstruction (x y : Bool) :
  let L : Fin 25 → Fin 18 := ![0,0,0,1,1,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,12,13,14]
  let R : Fin 25 → Fin 18 := ![1,2,3,2,14,3,15,5,6,7,6,9,7,8,9,11,10,11,16,13,13,15,17,14,15]
  let ends : Fin 25 → Sym2 (Fin 18) := fun e => s(L e,R e)
  let M : Finset (Fin 25) := {1,4,6,8,11,13,18,19,22}
  let bit : Fin 18 → Bool := ![true,false,true,false,true,false,true,false,false,false,x,false,y,false,false,false,x,y]
  ¬ ∃ (c : Fin 25 → Fin 6) (h : Fin 18 → Fin 25 → Fin 6),
    (∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → c e ≠ c f) ∧
    (∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f) ∧
    (∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → h v e ≠ c f) ∧
    (∀ e, (L e).val < 16 → (R e).val < 16 → ∀ f g,
      L e ∈ ends f → R e ∈ ends g → f ≠ e → g ≠ e → h (L e) f ≠ h (R e) g) ∧
    (∀ e ∈ M, c e = if bit (L e) then 1 else 0) ∧
    (∀ e ∉ M, 2 ≤ (c e).val) ∧
    (∀ e ∈ M, e ≠ 18 → e ≠ 22 →
      ¬ (h (L e) e = (if bit (L e) then 0 else 1) ∧
          h (R e) e = (if bit (R e) then 0 else 1))) ∧
    (∀ e ∉ M, h (L e) e ≠ (if bit (L e) then 0 else 1) →
      h (R e) e ≠ (if bit (R e) then 0 else 1) → c e = 2 ∨ c e = 3) := by
  set_option maxHeartbeats 4000000 in
    classical
    intro L R ends M bit
    rintro ⟨c,h,hcext,hhidden,havoid,hstrong,hmatch,hfactor,hexact,hglobal⟩
    let T : Fin 18 → Fin 3 → Fin 25 :=
      ![![0,2,1],![0,3,4],![3,5,1],![2,5,6],![7,9,8],![7,10,11],![10,12,8],![9,12,13],![14,15,13],![14,16,11],![16,17,18],![15,17,19],![20,21,22],![20,23,19],![23,24,4],![21,24,6],![18,18,18],![22,22,22]]
    let low : Fin 18 → Fin 6 := fun v => cycle_matching_low_color (!(bit v))
    let m : Fin 18 → ℕ := fun v => if h v (T v 2) = low v then 1 else 0
    have low_eq (v : Fin 18) : low v = if bit v then 0 else 1 := by
      cases hb : bit v <;> simp [low,cycle_matching_low_color,hb]
    have own : ∀ e ∈ M, e ≠ 18 → e ≠ 22 → m (L e) + m (R e) = 1 :=
      op874_open_four_square_retained_matching_owners x y c h hcext hhidden havoid hstrong hmatch hfactor hexact
    have middle : m 13 + m 14 + m 15 ≤ 1 ∧ m 8 + m 9 + m 11 ≤ 1 :=
      op874_open_four_square_middle_matching_owner_bounds x y c h hcext hhidden havoid hstrong hmatch hfactor hexact
    have global' : ∀ e ∉ M, h (L e) e ≠ low (L e) → h (R e) e ≠ low (R e) → c e = 2 ∨ c e = 3 := by
      intro e he ha hb
      apply hglobal e he
      · simpa only [← low_eq (L e)] using ha
      · simpa only [← low_eq (R e)] using hb
    have chord : m 0 + m 2 = 1 ∧ m 4 + m 6 = 1 := by
      constructor
      · exact own 1 (by decide) (by decide) (by decide)
      · exact own 8 (by decide) (by decide) (by decide)
    have outer : m 0 + m 1 + m 2 + m 3 ≤ 2 ∧ m 4 + m 5 + m 6 + m 7 ≤ 2 :=
      op874_open_four_square_outer_matching_owner_bounds x y c h hcext hhidden havoid hstrong hmatch hfactor global' chord
    have e1 : m 0 + m 2 = 1 := own 1 (by decide) (by decide) (by decide)
    have e4 : m 1 + m 14 = 1 := own 4 (by decide) (by decide) (by decide)
    have e6 : m 3 + m 15 = 1 := own 6 (by decide) (by decide) (by decide)
    have e8 : m 4 + m 6 = 1 := own 8 (by decide) (by decide) (by decide)
    have e11 : m 5 + m 9 = 1 := own 11 (by decide) (by decide) (by decide)
    have e13 : m 7 + m 8 = 1 := own 13 (by decide) (by decide) (by decide)
    have e19 : m 11 + m 13 = 1 := own 19 (by decide) (by decide) (by decide)
    let V : Fin 16 → Fin 18 := ![1,0,3,2,12,15,14,13,8,9,10,11,4,5,6,7]
    let z : Fin 16 → ℕ := fun i => m (V i)
    apply op874_four_squares_ownership_count_obstruction z
    · change m 0 + m 2 = 1; omega
    · change m 9 + m 5 = 1; omega
    · change m 3 + m 15 = 1; omega
    · change m 1 + m 14 = 1; omega
    · change m 4 + m 6 = 1; omega
    · change m 8 + m 7 = 1; omega
    · change m 13 + m 11 = 1; omega
    · change m 1 + m 0 + m 3 + m 2 ≤ 2; omega
    · change m 4 + m 5 + m 6 + m 7 ≤ 2; omega
    · change m 15 + m 14 + m 13 ≤ 1; omega
    · change m 8 + m 9 + m 11 ≤ 1; omega
