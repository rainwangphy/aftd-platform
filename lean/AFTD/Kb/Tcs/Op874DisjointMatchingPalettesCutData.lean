import AFTD.Prelude

/-!
# op874_disjoint_matching_palettes_cut_data

Topic: graphs   Node: 8a586fe0d0ea

Provenance: helper lemma. Finite data for the matching-palette obstruction in OP-874; https://arxiv.org/abs/2610.41950.

The displayed matching involution and cut on the eight-cycle give a simple cubic graph with a locally maximal matching cut; the matching contraction has a proper four-edge-coloring, and vertices 1 and 2 have the same bit.
-/

theorem op874_disjoint_matching_palettes_cut_data :
    let mate : Fin 8 → Fin 8 := ![6,4,7,5,1,3,0,2]
    let bit : Fin 8 → Bool := ![true,false,false,true,false,true,true,false]
    let w : Fin 8 → Fin 4 := ![3,2,3,1,0,2,1,0]
    Function.Involutive mate ∧
    (∀ v, mate v ≠ v ∧ mate v ≠ v-1 ∧ mate v ≠ v+1 ∧ bit (mate v) = bit v) ∧
    (∀ v, (if bit (v-1) = bit v then 1 else 0) +
          (if bit (v+1) = bit v then 1 else 0) +
          (if bit (mate v-1) = bit v then 1 else 0) +
          (if bit (mate v+1) = bit v then 1 else 0) ≤ (2 : ℕ)) ∧
    (∀ v, w (v-1) ≠ w v) ∧
    (∀ v, Function.Injective ![w (v-1),w v,w (mate v-1),w (mate v)]) ∧
    bit 1 = bit 2 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    fin_cases v <;> decide
  · decide
  · decide
  · decide
  · intro v i j h
    fin_cases v <;> fin_cases i <;> fin_cases j <;> simp_all
  · decide
